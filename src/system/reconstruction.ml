open Types.Base
open Types.Tvar
open Types.Additions
open Parsing.Variable
open Msc
open Annotations
open Utils
open Algorithmic

module Make () = struct

  module Aux = Reconstruction_aux.Make ()
  open Aux

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
  | TypeCoercion (_, t') when subtype (conj t') t -> [Env.empty]
  | Const c when subtype (typeof_const_atom tenv c) t -> [Env.empty]
  | Alias v when subtype (Env.find v env) t -> [Env.empty]
  | Alias _ | Abstract _ | TypeCoercion _ | Const _ -> []
  | Pair (v1, v2) ->
    pair_dnf t
    |> List.filter (fun b -> subtype (pair_branch_type b) t)
    |> List.map (
      fun (t1,t2) -> Env.construct_dup [(v1, t1) ; (v2, t2)]
    )
  | Projection (Fst, v) -> [Env.singleton v (mk_times (cons t) any_node)]
  | Projection (Snd, v) -> [Env.singleton v (mk_times any_node (cons t))]
  | Projection (Field label, v) ->
    [Env.singleton v (mk_record true [(label, cons t)])]
  | RecordUpdate (v, label, None) ->
    let t = cap t (record_any_without label) in
    record_dnf t
    |> List.map (fun b -> record_branch_type b)
    |> List.filter (fun ti -> subtype ti t)
    |> List.map (
      fun ti -> Env.singleton v (remove_field_info ti label)
    )
  | RecordUpdate (v, label, Some x) ->
    let t = cap t (record_any_with label) in
    record_dnf t
    |> List.map (fun b -> record_branch_type b)
    |> List.filter (fun ti -> subtype ti t)
    |> List.map (
      fun ti ->
        let field_type = get_field ti label in
        let ti = remove_field_info ti label in
        Env.construct_dup [(v, ti) ; (x, field_type)]
      )
  | TypeConstr (v, _) -> [Env.singleton v t]
  | App (v1, v2) ->
    let alpha = TVar.mk_poly None in
    Env.find v1 env |> dnf |> List.map (
      fun arrows ->
        let t1 = branch_type arrows in
        let constr = [ (t1, mk_arrow (TVar.typ alpha |> cons) (cons t)) ] in
        let res = tallying constr in
        res |> List.map (fun sol ->
          let t1 = apply_subst_simplify sol t1 in
          let t2 = Subst.find' sol alpha in
          let clean_subst = clean_type_subst ~pos:any ~neg:empty t2 in
          let t1 = Subst.apply clean_subst t1 in
          let t2 = Subst.apply clean_subst t2 in
          let pvars = TVarSet.union (vars_poly t1) (vars_poly t2) in
          let mono = monomorphize pvars in
          Env.construct_dup [(v1, t1) ; (v2, t2)] |> Env.apply_subst mono
        )
    )
    |> List.flatten
    |> List.filter (fun env -> Env.bindings env |>
        List.for_all (fun (_,t) -> not (is_undesirable t)))
  | Ite (v, s, v1, v2) ->
    [Env.construct_dup [(v,s);(v1,t)] ; Env.construct_dup [(v,neg s);(v2,t)]]
  | Let (_, v2) -> [Env.singleton v2 t]

(* ====================================== *)
(* ============== CACHING =============== *)
(* ====================================== *)

type 'a res =
| Ok of 'a
| Fail
| Split of Env.t * 'a * 'a
| Subst of (Env.t * bool (* Low priority default *)) * Subst.t list * 'a * 'a
| NeedVar of Variable.t * 'a * 'a
(* [@@deriving show] *)

let caching_status = Aux.caching_status
let set_caching_status = Aux.set_caching_status

type icache = { context: Env.t ; pannot: PartialAnnot.a ; res: PartialAnnot.a res }

let inter_cache = Hashtbl.create 100

let add_to_inter_cache x env pannot res =
  if Aux.caching_status () then
    let fv = fv_def x in
    let env = Env.restrict (VarSet.elements fv) env in
    Hashtbl.add inter_cache x { context=env; pannot=pannot; res=res }

let get_inter_cache x env pannot =
  if Aux.caching_status () then
    let fv = fv_def x in
    let env = Env.restrict (VarSet.elements fv) env in
    let caches = Hashtbl.find_all inter_cache x in
    caches |> List.find_opt
      (fun ic -> PartialAnnot.equals_a pannot ic.pannot && Env.equiv env ic.context)
    |> Option.map (fun ic -> ic.res)
  else None

let clear_cache () =
  Hashtbl.clear inter_cache

(* ====================================== *)
(* ============ MAIN SYSTEM ============= *)
(* ====================================== *)

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

let generalize_inferable tvars =
  let tvars = TVarSet.filter TVar.can_infer tvars in
  generalize tvars

let mono_tvars env = Env.tvars env |> TVarSet.filter TVar.is_mono

let lambda_tvars env =
  env |> Env.filter (fun x _ -> Variable.is_lambda_var x) |> Env.tvars
  |> TVarSet.filter TVar.is_mono  

let simplify_tallying_infer env res_type sols =
  let tvars = mono_tvars env in
  let vars_involved dom sol =
    let sol = Subst.restrict sol dom in
    TVarSet.union (Subst.codom sol) dom
  in
  let leq_sol (_,r1) (_,r2) =
    let r1 = Subst.apply (vars r1 |> generalize) r1 in
    subtype_poly r1 r2
  in
  let order sols =
    let arr = Array.of_list sols in
    let elts = 0 -- ((Array.length arr) - 1) in
    let inst = elts |> add_others |> List.map (fun (e,es) ->
      let t = arr.(e) in
      let edges = es |> List.filter (fun e' -> leq_sol (arr.(e')) t) in
      (e,edges)
    ) in
    Tsort.sort_strongly_connected_components inst
    |> List.flatten |> List.map (fun e -> arr.(e))
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
  (* Simplify and make it reuse the same tvars if possible (better for caching) *)
  |> List.map (fun (sol, res) ->
    List.fold_left (fun (sol, res) v ->
      let t = Subst.find' sol v in
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
  (* Order solutions (more precise results first) *)
  |> order
  (* Printing (debug) *)
  (* |> (fun res ->
    Format.printf "=== Solutions ===@." ;
    Format.printf "with tvars=%a@." TVarSet.pp tvars ;
    res |> List.iter (fun (s,r) -> Format.printf "%a@.res:%a@." Subst.pp s pp_typ r) ;
    res
  ) *)
  |> List.map fst

let infer_mono_inter expl' infer_branch (b1, b2, (expl, tf,ud)) =
  let uNb = List.length b1 and eNb = List.length b2 in
  let nontrivial = uNb + eNb > 1 in
  if nontrivial then begin
    log ~level:0 "Typing intersection with %n unexplored branches (and %n explored).@." uNb eNb
  end ;
  let rec aux explored expl pending =
    match pending with
    | [] when explored = [] -> log ~level:3 "Intersection generated a fail (0 branch)@." ; Fail
    | [] -> Ok ([], explored, (expl, true, ud))
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

let merge_substs env apply_subst_branch mk_inter ((d,lpd), lst, pannot, default) =
  let tvars = lambda_tvars env in
  let lst = lst
    |> List.filter_map (fun s ->
      let d' = Env.apply_subst s d in
      if List.for_all2 (fun (_, t) (_, t') ->
        is_undesirable t || not (is_undesirable t')
      ) (Env.bindings d) (Env.bindings d')
      then Some (apply_subst_branch s pannot, Domains.singleton tvars d', false)
      else None)
  in
  log ~level:2 "@.Creating an intersection with %n branches.@." (List.length lst + 1) ;
  (* NOTE: it is important for the default case to be inserted at the end (smaller priority) *)
  mk_inter (lst@[default, Domains.singleton tvars d, lpd]) [] (Domains.empty,false,false)

let should_iterate env apply_subst_branch mk_inter res =
  match res with
  | Split (gamma, pannot, _) when Env.is_empty gamma -> Some pannot
  | Subst (info, lst, pannot, default) ->
    let tvars = mono_tvars env in
    if lst |> List.for_all (fun s -> TVarSet.inter (Subst.dom s) tvars |> TVarSet.is_empty)
    then Some (merge_substs env apply_subst_branch mk_inter
                (info, lst, pannot, default))
    else None
  | _ -> None

let rec infer_mono_a vardef tenv expl env pannot_a a =
  let memvar v = Env.mem v env in
  let vartype v = Env.find v env in
  let needvar v a1 a2 = NeedVar (v, a1, a2) in
  (* TODO: enable the lpd flag? (prune some uninteresting branches) *)
  let needsubst ss a1 a2 = Subst ((Env.empty, (*true*) false), ss, a1, a2) in
  let needsubst_no_lpd ss a1 a2 = Subst ((Env.empty, false), ss, a1, a2) in
  let rec aux pannot_a a =
    let open PartialAnnot in
    match a, pannot_a with
    | a, InterA i ->
      let aux expl pannot_a = infer_mono_a_iterated vardef tenv expl env pannot_a a in
      infer_mono_inter expl aux i
      |> map_res (fun x -> InterA x)
    | _, TypA -> Ok (TypA)
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
        let res = tallying_infer [(vartype v, disj s)] in
        let res = simplify_tallying_infer env empty res in
        needsubst res ConstrA UntypA
      else
        needvar v InferA UntypA
    | TypeConstr (v, s), ConstrA ->
      let tv = vartype v in
      let rec split_if_needed ts =
        match ts with
        | [] | [_] -> Ok TypA
        | s::ts when subtype tv s || disjoint tv s ->
          split_if_needed ts
        | s::_ -> Split (Env.singleton v s, ConstrA, ConstrA)
      in
      split_if_needed s
    | TypeCoercion (v, s), InferA ->
      if memvar v then
        begin match subtypes_expand (vartype v) s with
        | None -> Fail
        | Some _ -> Ok TypA
        end
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
        if subtype t empty then Ok TypA
        else if subtype t tau
        then
          let res = tallying_infer [(t, empty)] in
          let res = simplify_tallying_infer env empty res in
          if List.exists Subst.is_identity res
          then Ok TypA
          else needsubst_no_lpd res TypA ThenVarA
        else if subtype t (neg tau)
        then
          let res = tallying_infer [(t, empty)] in
          let res = simplify_tallying_infer env empty res in
          if List.exists Subst.is_identity res
          then Ok TypA
          else needsubst_no_lpd res TypA ElseVarA
        else Split (Env.singleton v tau, InferA, InferA)
      else needvar v InferA UntypA
    | Ite (_, _, v1, _), ThenVarA ->
      if memvar v1 then Ok TypA else needvar v1 TypA UntypA
    | Ite (_, _, _, v2), ElseVarA ->
      if memvar v2 then Ok TypA else needvar v2 TypA UntypA
    | Lambda (ts, _, _), InferA ->
      let pannot_a_s = List.map (fun t -> LambdaA (t, Infer)) ts in
      let pannot_a = match pannot_a_s with
      | [pannot_a] -> pannot_a
      | pannot_a_s ->
        let branches = pannot_a_s |> List.map (fun t -> (t, Domains.empty, false)) in
        InterA (branches, [], (Domains.empty, false, true))
      in
      aux pannot_a a
    | Lambda (_, v, e), LambdaA (s, pannot) ->
      log ~level:2 "Entering lambda for %a with domain %a.@." Variable.pp v pp_typ s ;
      if is_empty s then (log ~level:3 "Lambda with empty domain generated a fail.@." ; Fail)
      else
        let env = Env.add v s env in
        infer_mono_iterated tenv (Domains.enter_lambda v s expl) env pannot e
        |> map_res (fun x -> LambdaA (s, x))
        |> (fun res -> match res with
          | Subst ((env',b), ss, pannot1, pannot2) ->
            Subst ((Env.add v s env',b), ss, pannot1, pannot2)
          | res -> res
        )
    | _, _ -> assert false
  in
  aux pannot_a a

and infer_mono tenv expl env pannot e =
  let memvar v = Env.mem v env in
  let needvar v a1 a2 = NeedVar (v, a1, a2) in
  let open PartialAnnot in
  let rec aux pannot e =
    match e, pannot with
    | _, Untyp -> log ~level:3 "Untyp annot generated a fail.@." ; Fail
    | _, Typ -> Ok Typ
    | Var v, Infer ->
      if memvar v then Ok Typ else needvar v Infer Untyp
    | Bind _, Inter i ->
      let aux expl pannot = infer_mono_iterated tenv expl env pannot e in
      infer_mono_inter expl aux i
      |> map_res (fun x -> Inter x)
    | Bind _, Infer -> aux (TrySkip Infer) e
    | Bind (v, _, e) as ee, TrySkip pannot ->
      begin match infer_mono_iterated tenv expl env pannot e with
      | NeedVar (v', pannot1, pannot2) when Variable.equals v v' ->
        log ~level:0 "Var %a needed.@." Variable.pp v ;
        aux (TryKeep (InferA, pannot1, pannot2)) ee
      | Ok pannot -> Ok (Skip pannot)
      | res -> map_res (fun x -> TrySkip x) res
      end
    | Bind (v, _, e) as ee, Skip pannot ->
      begin match infer_mono_iterated tenv expl env pannot e with
      | NeedVar (v', _, pannot2) when Variable.equals v v' ->
        aux (Skip pannot2) ee
      | res -> map_res (fun x -> Skip x) res
      end
    | Bind (v, a, _), TryKeep (pannot_a, pannot1, pannot2) ->
      log ~level:1 "Trying to type var %a.@." Variable.pp v ;
      begin match infer_mono_a_iterated v tenv expl env pannot_a a with
      | Ok pannot_a ->
        let pannot = Keep (pannot_a, ([(any, pannot1)], [], [])) in
        aux pannot e
      | Fail -> aux (Skip pannot2) e
      | res -> map_res (fun x -> TryKeep (x, pannot1, pannot2)) res
      end
    | Bind (v,_,_), Propagate (pannot_a, (envs1,typ1,t1), (envs2,typ2,t2), union) ->
      let add_to_ex_u exs us (ex,d,u) = (exs@ex,d,us@u) in
      let find_compat envs =
        envs |> Utils.find_among_others (fun env' _ -> is_compatible env env')
      in
      let propagate =
        match find_compat envs1 with
        | Some (env,envs) -> Some (env,envs,envs2,(typ2, t2),typ1)
        | None ->
          begin match find_compat envs2 with
          | Some (env,envs) -> Some (env,envs1,envs,(typ1, t1),typ2)
          | None -> None
          end
      in
      begin match propagate with
      | Some (env',envs1,envs2,ex,u) ->
        log ~level:1 "Var %a is ok but its DNF needs a split.@." Variable.pp v ;
        let pannot1 = Keep (pannot_a, add_to_ex_u [ex] [u] union) in
        let pannot2 = Propagate (pannot_a, (envs1,typ1,t1), (envs2,typ2,t2), union) in
        let env' = Env.filter (fun v t -> subtype_poly (Env.find v env) t |> not) env' in
        Split (env', pannot1, pannot2)
      | None -> aux (Keep (pannot_a, add_to_ex_u [(typ1, t1);(typ2,t2)] [] union)) e
      end
    | Bind (v, a, e), Keep (pannot_a, splits) ->
      let annot_a = infer_poly_a v tenv env pannot_a a in
      let t = typeof_a_nofail v tenv env annot_a a in
      log ~level:1 "Var %a typed with type %a.@." Variable.pp v pp_typ t ;  
      let keep = map_res (fun x -> Keep (pannot_a, x)) in
      let rec aux_splits splits =
        match splits with
        | ([],[],_) -> assert false
        | ([],d,u) -> Ok (Keep (pannot_a, ([],d,u)))
        | ((s,_)::ex,d,u) when (ex <> [] || d <> []) && disjoint t s ->
          aux_splits (ex,d,s::u)
        | ((s,pannot)::ex,d,u) ->
          let t = cap_o t s in
          log ~level:1 "Exploring split %a for %a.@." pp_typ s Variable.pp v ;
          begin match infer_mono_iterated tenv expl (Env.add v t env) pannot e with
          | Ok pannot -> aux_splits (ex,(s, pannot)::d,u)
          | Split (env', pannot1, pannot2) when Env.mem v env' ->
            let s' = Env.find v env' in
            let t1 = cap_o s s' |> simplify_typ in
            let t2 = diff_o s s' |> simplify_typ in
            let gammas1 = refine_a tenv env a (neg t1) in
            let gammas2 = refine_a tenv env a (neg t2) in
            let res1 =
              Propagate (pannot_a,(gammas1,t1,pannot1),(gammas2,t2,pannot2),(ex,d,u))
            in
            let res2 = Keep (pannot_a, ((s,pannot2)::ex,d,u)) in
            Split (Env.rm v env', res1, res2)
          | res -> res |> map_res (fun x -> ((s, x)::ex,d,u)) |> keep
          end
      in
      aux_splits splits
    | _, _ -> assert false
  in
  aux pannot e

and infer_mono_a_iterated vardef tenv expl env pannot_a a =
  let open PartialAnnot in
  match get_inter_cache vardef env pannot_a with
  | Some res -> res
  | None ->
    log ~level:5 "infer_mono_a_iterated@." ;
    let res = infer_mono_a vardef tenv expl env pannot_a a in
    let si =
      should_iterate env apply_subst_a
        (fun a b c -> InterA (a,b,c)) res
    in
    let res = match si with
    | None -> res
    | Some pannot_a -> infer_mono_a_iterated vardef tenv expl env pannot_a a
    in
    add_to_inter_cache vardef env pannot_a res ;
    res

and infer_mono_iterated tenv expl env pannot e =
  let open PartialAnnot in
  log ~level:5 "infer_mono_iterated@." ;
  let res = infer_mono tenv expl env pannot e in
  let si =
    should_iterate env apply_subst
      (fun a b c -> Inter (a,b,c)) res
  in
  match si with
  | None -> res
  | Some pannot -> infer_mono_iterated tenv expl env pannot e

(* ====================================== *)
(* ================ INFER =============== *)
(* ====================================== *)

let infer tenv env e =
  let open PartialAnnot in
  Aux.init_fv_htbl e ;
  let initial_pannot = Infer in
  let res =
    match infer_mono_iterated tenv Domains.empty env initial_pannot e with
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
  in
  clear_cache () ; Aux.clear_cache () ; res

let typeof_infer tenv env e =
  let annot = infer tenv env e in
  (* let annot = FullAnnot.clear_cache annot in *)
  typeof_nofail tenv env annot e

end