open Types.Base
open Types.Tvar
open Types.Additions
open Parsing.Variable
open Msc
open Annotations
open Utils
open Algorithmic

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

let infer_poly_inter infer_poly_branch (b1, b2, (_,tf,_)) =
  assert (b1 = [] && b2 <> [] && tf) ;
  b2 |> List.map infer_poly_branch

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
    ConstrA [tallying_one [(vartype v, s)]]
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
    let res = simplify_tallying (TVar.typ alpha) res in
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
  | Bind (_, _, e), PartialAnnot.Skip pannot ->
    let annot = infer_poly tenv env pannot e in
    FullAnnot.Skip annot
  | Bind (v, a, e), PartialAnnot.Keep (pannot_a, (ex,d,u), _) ->
    assert (d <> [] && ex = []) ;
    let annot_a = infer_poly_a v tenv env pannot_a a in
    let t = typeof_a_nofail v tenv env annot_a a in
    assert (subtype any (u@(List.map fst d) |> disj)) ;
    let branches = d |> List.map (fun (si, pannot) ->
        let t = cap_o t si in
        let env = Env.add v t env in
        (si, infer_poly tenv env pannot e)
      )
    in
    let inst = u |> List.map (fun u -> tallying_one [(t, neg u)]) in
    FullAnnot.Keep (annot_a, branches, inst)
  | _, _ ->  assert false
