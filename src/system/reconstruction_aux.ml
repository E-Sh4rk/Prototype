open Types.Base
open Types.Tvar
open Types.Additions
open Parsing.Variable
open Msc
open Annotations
open Utils
open Algorithmic

module Make () = struct

(* ====================================== *)
(* ============== CACHING =============== *)
(* ====================================== *)

let fv_def_htbl = Hashtbl.create 100
let fv_body_htbl = Hashtbl.create 100
let init_fv_htbl =
  let rec init_a v a =
    Hashtbl.add fv_def_htbl v (Msc.fv_a a) ;
    match a with
    | Lambda (_,_,e) -> init e
    | _ -> ()
  and init e =
    match e with
    | Var _ -> ()
    | Bind (v, a, e) ->
      Hashtbl.add fv_body_htbl v (Msc.fv_e e) ;
      init_a v a ; init e
  in
  init

let fv_def v = Hashtbl.find fv_def_htbl v
let fv_body v = Hashtbl.find fv_body_htbl v

let invalidate c = { c with PartialAnnot.env_changed = true }

let invalidate_cache_inter f (pending, expl, flags) =
  let pending = pending |> List.map (fun (branch,d,b) -> (f branch,d,b)) in
  let expl = expl |> List.map f in
  (pending, expl, flags)

let rec invalidate_cache_a v bind_var a (pannot_a, c_a) =
  let open PartialAnnot in
  let depends_on = fv_def bind_var in
  if VarSet.mem v depends_on then
    let pannot_a =
      match pannot_a, a with
      | LambdaA (ty, pannot, dc), Lambda (_,_,e) ->
        LambdaA (ty, invalidate_cache v e pannot, dc)
      | _, _ -> pannot_a
    in
    (pannot_a, invalidate c_a)
  else (pannot_a, c_a)

and invalidate_cache v e (pannot, c) =
  let open PartialAnnot in
  match e with
  | Var v' when Variable.equals v v' -> (pannot, invalidate c)
  | Var _ -> (pannot, c)
  | Bind (v', a, e) ->
    assert (Variable.equals v v' |> not) ;
    let fv = VarSet.union (fv_body v') (fv_def v') in
    if VarSet.mem v fv then
      let treat_union (ex,d,u) =
        let aux (ty, t) = (ty, invalidate_cache v e t) in
        (List.map aux ex, List.map aux d, u)
      in
      let pannot =
        begin match pannot with
        | Infer -> Infer
        | Skip pannot -> Skip (invalidate_cache v e pannot)
        | TrySkip pannot -> TrySkip (invalidate_cache v e pannot)
        | Keep (pannot_a, union, dc) ->
          let pannot_a = invalidate_cache_a v v' a pannot_a in
          let union = treat_union union in
          Keep (pannot_a, union, dc)
        | TryKeep (pannot_a, pannot1, pannot2) ->
          let pannot_a = invalidate_cache_a v v' a pannot_a in
          let pannot1 = invalidate_cache v e pannot1 in
          let pannot2 = invalidate_cache v e pannot2 in
          TryKeep (pannot_a, pannot1, pannot2)
        | Propagate (pannot_a, lst, union, dc) ->
          let pannot_a = invalidate_cache_a v v' a pannot_a in
          let union = treat_union union in
          Propagate (pannot_a, lst, union, dc)
        | Inter i ->
          Inter (invalidate_cache_inter (invalidate_cache v e) i)
        | _ -> assert false
        end
      in
      (pannot, invalidate c)
    else (pannot, c)

(* ====================================== *)
(* ============= POLY INFER ============= *)
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
let approximate_app ~infer t1 t2 resvar =
  (* let is_poly = if infer then TVar.can_infer else TVar.is_poly in
  let t1s = approximate_arrow is_poly t1 in *)
  (* NOTE: this approximation is disabled (it does not seem to have a big impact
     on classical examples, and it can produce weaker types) *)
  let t1s = [t1] in
  let res =
    t1s |> List.map (fun t1 -> approximate_app infer t1 t2 resvar) |> List.flatten
  in
  if res = [] && List.length t1s > 1
  then approximate_app infer t1 t2 resvar
  else res

let infer_poly_inter infer_poly_branch (b1, b2, (d,tf,ud)) =
  assert (b1 = [] && b2 <> [] && tf) ;
  let (b2, annots) = b2 |> List.map infer_poly_branch |> List.split in
  ((b1,b2,(d,tf,ud)), annots)

let cached c =
  let open PartialAnnot in
  if c.annot_changed || c.env_changed
  then None
  else c.prev_fa

let rec infer_poly_a vardef tenv env (pannot_a, c_a) a =
  let open PartialAnnot in
  let open FullAnnot in
  match cached c_a with
  | Some annot_a -> ((pannot_a, c_a), annot_a)
  | None ->
    let vartype v = Env.find v env in
    let (pannot_a, annot_a) = match a, pannot_a with
    | a, PartialAnnot.InterA i ->
      let (pannots_a, annots_a) = infer_poly_inter
        (fun pannot_a -> infer_poly_a vardef tenv env pannot_a a) i
      in
      (PartialAnnot.InterA pannots_a, InterA annots_a)
    | Alias _, TypA -> (TypA, AliasA)
    | Const _, TypA -> (TypA, ConstA)
    | Let _, TypA -> (TypA, LetA)
    | Abstract _, TypA -> (TypA, AbstractA)
    | Pair (v1, v2), TypA ->
      let r1 = refresh (vartype v1 |> vars_poly) in
      let r2 = refresh (vartype v2 |> vars_poly) in
      (TypA, PairA (r1, r2))
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
      (TypA, ProjA res)
    | RecordUpdate (v, _, None), TypA ->
      let res = tallying_nonempty [(vartype v, record_any)] in
      let res = simplify_tallying record_any res in
      (TypA, RecordUpdateA (res, None))
    | RecordUpdate (v, _, Some v2), TypA ->
      let res = tallying_nonempty [(vartype v, record_any)] in
      let res = simplify_tallying record_any res in
      let r = refresh (vartype v2 |> vars_poly) in
      (TypA, RecordUpdateA (res, Some r))
    | TypeConstr (v, s), TypA ->
      (TypA, ConstrA [tallying_one [(vartype v, s)]])
    | App (v1, v2), TypA ->
      let t1 = vartype v1 in
      let t2 = vartype v2 in
      let r1 = refresh (vars_poly t1) in
      let r2 = refresh (vars_poly t2) in
      let t1 = Subst.apply r1 t1 in
      let t2 = Subst.apply r2 t2 in
      let alpha = TVar.mk_poly None in
      let arrow_type = mk_arrow (cons t2) (TVar.typ alpha |> cons) in
      log ~level:4 "@.Approximate tallying for %a: %a <= %a@."
        Variable.pp vardef pp_typ t1 pp_typ arrow_type ;
      let res = approximate_app ~infer:false t1 t2 alpha in
      if List.length res = 0 then Format.printf "ERROR: %a@.%a@." pp_typ t1 pp_typ t2 ;
      (* TODO: fix Assertion failed *)
      assert (List.length res > 0) ;
      let res = simplify_tallying (TVar.typ alpha) res in
      let (s1, s2) = res |> List.map (fun s ->
        (Subst.compose_restr s r1, Subst.compose_restr s r2)
      ) |> List.split in
      (TypA, AppA (s1, s2))
    | Ite (v, _, _, _), EmptyA ->
      (EmptyA, EmptyA [tallying_one [(vartype v, empty)]])
    | Ite (v, s, _, _), ThenA ->
      (ThenA, ThenA [tallying_one [(vartype v, s)]])
    | Ite (v, s, _, _), ElseA ->
      (ElseA, ElseA [tallying_one [(vartype v, neg s)]])
    | Lambda (_, v, e), PartialAnnot.LambdaA (s, pannot, dc) ->
      let pannot =
        if def_typ_unchanged dc s
        then pannot else invalidate_cache v e pannot
      in
      let dc = def_cache s in
      let env = Env.add v s env in
      let (pannot, annot) = infer_poly tenv env pannot e in
      (LambdaA (s, pannot, dc), LambdaA (s, annot))
    | _, _ ->  assert false
    in
    let annot_a = (annot_a, init_cache ()) in
    ((pannot_a, cache annot_a), annot_a)

and infer_poly tenv env (pannot, c) e =
  let open PartialAnnot in
  let open FullAnnot in
  match cached c with
  | Some annot -> ((pannot, c), annot)
  | None ->
    let vartype v = Env.find v env in
    let (pannot, annot) = match e, pannot with
    | e, PartialAnnot.Inter i ->
      let (pannots, annots) = infer_poly_inter
        (fun pannot -> infer_poly tenv env pannot e) i
      in
      (PartialAnnot.Inter pannots, Inter annots)
    | Var v, Typ ->
      let r = refresh (vartype v |> vars_poly) in
      (Typ, BVar r)
    | Bind (_, _, e), PartialAnnot.Skip pannot ->
      let (pannot, annot) = infer_poly tenv env pannot e in
      (Skip pannot, Skip annot)
    | Bind (v, a, e), PartialAnnot.Keep (pannot_a, (ex,d,u), dc) ->
      assert (d <> [] && ex = []) ;
      let (pannot_a, annot_a) = infer_poly_a v tenv env pannot_a a in
      let t = typeof_a_nofail v tenv env annot_a a in
      assert (subtype any (u@(List.map fst d) |> disj)) ;
      let d =
        if def_typ_unchanged dc t
        then d
        else
          let inv = invalidate_cache v e in
          d |> List.map (fun (s,t) -> (s, inv t))
      in  
      let dc = def_cache t in
      let (d, branches) = d |> List.map (fun (si, pannot) ->
          let t = cap_o t si in
          let env = Env.add v t env in
          let (pannot, annot) = infer_poly tenv env pannot e in
          ((si, pannot), (si, annot))
        ) |> List.split
      in
      let inst = u |> List.map (fun u -> tallying_one [(t, neg u)]) in
      (Keep (pannot_a, (ex,d,u), dc), Keep (annot_a, branches, inst))
    | _, _ ->  assert false
    in
    let annot = (annot, init_cache ()) in
    ((pannot, cache annot), annot)

end