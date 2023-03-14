open Types.Base
open Types.Tvar
open Types.Additions
open Common
open Parsing.Variable
open Msc
open Annotations
open Utils

(* TODO: solve issues with examples in test.ml: and2_, curried14, etc. *)

(* ====================================== *)
(* =============== TYPEOF =============== *)
(* ====================================== *)

exception Untypeable of Position.t list * string

let typeof_const_atom tenv c =
  match c with
  | Parsing.Ast.Atom str -> get_atom_type tenv str
  | c -> Parsing.Ast.const_to_typ c

let unbound_variable v =
  raise (Untypeable (Variable.get_locations v, "Unbound variable "^(Variable.show v)^"."))
  
let var_type v env =
  if Env.mem v env then Env.find v env else unbound_variable v

let instantiate_check pos ss t =
  let check_s s =
    Subst.dom s |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty
  in
  if List.for_all check_s ss
  then instantiate ss t
  else raise (Untypeable (pos, "Invalid instantiation: attempting to substitute a monomorphic variable."))

let check_mono pos t =
  if is_mono_typ t
  then ()
  else raise (Untypeable (pos, "Invalid type: lambda domains and splits should be monomorphic."))

let rename_check pos r t =
  if Subst.is_renaming r &&
    Subst.dom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty &&
    Subst.codom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty
  then Subst.apply r t
  else raise (Untypeable (pos, "Invalid renaming."))

(* TODO: test examples in flatten.ml, and merge them with test.ml *)
let typeof_inter typeof_branch pos branches =
  let untypeable str = raise (Untypeable (pos, str)) in
  if branches = []
  then untypeable ("Invalid intersection: there must be at least 1 branch.")
  else
    branches
    |> List.map (fun annot -> typeof_branch annot)
    |> conj_o

let rec typeof_a vardef tenv env annot_a a =
  let open FullAnnot in
  let pos = Variable.get_locations vardef in
  let var_type v = var_type v env in
  let rename_check = rename_check pos in
  let instantiate_check = instantiate_check pos in
  let untypeable str = raise (Untypeable (pos, str)) in
  begin match a, annot_a with
  | a, InterA branches ->
    typeof_inter (fun annot_a -> typeof_a vardef tenv env annot_a a) pos branches
  | Alias v, AliasA -> var_type v
  | Const c, ConstA -> typeof_const_atom tenv c
  | Abstract t, AbstractA -> t
  | Pair (v1, v2), PairA (r1, r2) ->
    let t1 = var_type v1 |> rename_check r1 in
    let t2 = var_type v2 |> rename_check r2 in
    mk_times (cons t1) (cons t2)
  | Projection (Field label, v), ProjA ss ->
    let t = var_type v |> instantiate_check ss in
    if subtype t record_any
    then
      try get_field t label
      with Not_found ->
        untypeable ("Invalid projection: missing label " ^ label ^ ".")
    else untypeable ("Invalid projection: not a record.")
  | Projection (p, v), ProjA ss ->
    let t = var_type v |> instantiate_check ss in
    if subtype t pair_any
    then (if p = Fst then pi1 t else pi2 t)
    else untypeable ("Invalid projection: not a pair.")
  | RecordUpdate (v, label, None), RecordUpdateA (ss, None) ->
    let t = var_type v |> instantiate_check ss in
    if subtype t record_any
    then remove_field t label
    else untypeable ("Invalid field deletion: not a record.")
  | RecordUpdate (v, label, Some v'), RecordUpdateA (ss, Some r) ->
    let t = var_type v |> instantiate_check ss in
    if subtype t record_any
    then
      let t' = var_type v' |> rename_check r in
      let right_record = mk_record false [label, cons t'] in
      merge_records t right_record  
    else untypeable ("Invalid field update: not a record.")
  | TypeConstr (v, s), ConstrA ss ->
    let t = var_type v in
    if subtype (instantiate_check ss t) s
    then t
    else untypeable ("Type constraint not satisfied.")
  | App (v1, v2), AppA (ss1, ss2) ->
    let apply t1 t2 =
      if subtype t1 arrow_any
      then
        if subtype t2 (domain t1)
        then apply t1 t2
        else untypeable ("Invalid application: argument not in the domain.")
      else untypeable ("Invalid application: not a function.")
    in
    (* NOTE: Approximation... this is not what the paper suggests,
       but given the inference we gain nothing by doing like in the paper. *)
    let treat_sigma (s1,s2) =
      let t1 = var_type v1 |> instantiate_check [s1] in
      let t2 = var_type v2 |> instantiate_check [s2] in
      apply t1 t2
    in
    List.combine ss1 ss2 |> List.map treat_sigma |> conj_o
    (* let t1 = var_type v1 |> instantiate_check ss1 in
    let t2 = var_type v2 |> instantiate_check ss2 in
    apply t1 t2 *)
  | Ite (v, _, _, _), EmptyA ->
    let t = var_type v in
    if is_empty t then empty
    else untypeable ("Invalid typecase: tested expression is not empty.")
  | Ite (v, s, v1, _), ThenA ->
    let t = var_type v in
    if subtype t s
    then var_type v1
    else untypeable ("Invalid typecase: tested expression hasn't the required type.")
  | Ite (v, s, _, v2), ElseA ->
    let t = var_type v in
    if subtype t (neg s)
    then var_type v2
    else untypeable ("Invalid typecase: tested expression hasn't the required type.")
  | Let (v1, v2), LetA ->
    if Env.mem v1 env
    then var_type v2
    else untypeable ("Invalid let binding: definition has not been typed.")
  | Lambda (_, v, e), LambdaA (s, annot) ->
    check_mono pos s ;
    let env = Env.add v s env in
    let t = typeof tenv env annot e in
    mk_arrow (cons s) (cons t)
  | _, _ -> untypeable ("Invalid annotations.")
  end
  |> bot_instance |> simplify_typ
  
and typeof tenv env annot e =
  let open FullAnnot in
  begin match e, annot with
  | e, Inter branches ->
    typeof_inter (fun annot -> typeof tenv env annot e) [] branches
  | Var v, BVar r -> var_type v env |> rename_check [] r
  | Bind (v, _, e), Skip annot ->
    assert (Env.mem v env |> not) ;
    typeof tenv env annot e
  | Bind (v, a, e), Keep (annot_a, (splits, inst)) ->
    let t = typeof_a v tenv env annot_a a in
    let pos = Variable.get_locations v in
    let untypeable str = raise (Untypeable (pos, str)) in
    if splits = []
    then untypeable ("Invalid decomposition: there must be at least 1 branch.")
    else
      if subtype (instantiate_check pos inst t)
        (splits |> List.map fst |> disj)
      then
        splits |> List.map (fun (s, annot) ->
          check_mono pos s ;
          let env = Env.add v (cap t s) env in
          typeof tenv env annot e
        ) |> disj_o
      else untypeable ("Invalid decomposition: does not cover the whole domain.")
  | _, _ -> raise (Untypeable ([], "Invalid annotations."))
  end
  |> bot_instance |> simplify_typ

let typeof_a_nofail vardef tenv env annot_a a =
  try typeof_a vardef tenv env annot_a a
  with Untypeable (_, str) -> Format.printf "%a: %s@." pp_a a str ; assert false

let typeof_nofail tenv env annot e =
  try typeof tenv env annot e
  with Untypeable (_, str) -> Format.printf "%a: %s@." pp_e e str ; assert false  

(* ====================================== *)
(* =============== REFINE =============== *)
(* ====================================== *)

let rec is_undesirable s =
  subtype s arrow_any &&
  dnf s |> List.for_all
    (List.exists (fun (a, b) -> non_empty a && is_undesirable b))

let specific_inst t =
  let s = vars_poly t |> TVarSet.destruct
    |> List.map (fun v -> (v, empty)) |> Subst.construct in
  Subst.apply s t

let refine_a tenv env a t =
  log ~level:5 "refine_a@." ;
  match a with
  | Lambda _ -> []
  | Abstract t' when subtype t' t -> [Env.empty]
  | Const c when subtype (typeof_const_atom tenv c) t -> [Env.empty] 
  | Alias v when subtype (Env.find v env) t -> [Env.empty]
  | Alias _ | Abstract _ | Const _ -> []
  | Pair (v1, v2) ->
    split_pair t
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
      let t1 = apply_subst_simplify sol t1 in
      let t2 = Subst.find' sol alpha in
      let clean_subst = clean_type_subst ~pos:any ~neg:empty t2 in
      let t1 = Subst.apply clean_subst t1 in
      let t2 = Subst.apply clean_subst t2 in
      Env.construct_dup [ (v1, t1 |> specific_inst) ; (v2, t2) ]
    )
    |> List.filter (fun env -> env |> Env.tvars
        |> TVarSet.filter TVar.is_poly |> TVarSet.is_empty)
    |> List.filter (fun env -> Env.bindings env |>
        List.for_all (fun (_,t) -> not (is_undesirable t)))
  | Ite (v, s, v1, v2) ->
    [Env.construct_dup [(v,s);(v1,t)] ; Env.construct_dup [(v,neg s);(v2,t)]]
  | Let (_, v2) -> [Env.singleton v2 t]

(* ====================================== *)
(* =============== INFER I ============== *)
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
    match k with
    | `Pos -> Some (v', TVar.typ v)
    | `Neg -> Some (v', TVar.typ v |> neg)
    | `Both -> None
    else None
    ) |> Subst.construct

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
    (* Simplify (light) *)
    let sol =
      List.fold_left (fun sol v ->
        let t = Subst.find' sol v in
        (* let v = TVar.mk_fresh v in *)
        let s = replace_vars t (top_vars t |> TVarSet.filter TVar.is_poly) v in
        Subst.compose s sol
      ) sol (Subst.dom sol |> TVarSet.destruct)
    in
    (* Decorrelate solutions *)
    (* NOTE: Disabled because it can cause two branches
       with a common domain to separate *)
    (* let t = Subst.apply sol res in
    let s = refresh_all (vars_poly t) in
    Subst.compose s sol *)
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
      dnf t |> simplify_dnf |> List.map (fun arrows ->
          (* Keep all branches with no var in their domain, split the others *)
          (* let (keep, split) = arrows |> List.partition (fun (a,_) ->
            vars a |> TVarSet.filter is_poly |> TVarSet.is_empty)
          in *)
          let (keep, split) = ([], arrows) in
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

let infer_inst_inter infer_inst_branch (b1, b2, tf) =
  assert (b2 = [] && b1 <> [] && tf) ;
  b1 |> List.map (fun (annot,_,_) -> infer_inst_branch annot)

let rec infer_inst_a vardef tenv env pannot_a a =
  let open PartialAnnot in
  let open FullAnnot in
  let vartype v = Env.find v env in
  match a, pannot_a with
  | a, PartialAnnot.InterA i ->
    InterA (infer_inst_inter (fun pannot_a -> infer_inst_a vardef tenv env pannot_a a) i)
  | Alias _, TypA -> AliasA
  | Const _, TypA -> ConstA
  | Let _, TypA -> LetA
  | Abstract _, TypA -> AbstractA
  | Pair (v1, v2), TypA ->
    let r1 = refresh_all (vartype v1 |> vars_poly) in
    let r2 = refresh_all (vartype v2 |> vars_poly) in
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
    let r = refresh_all (vartype v2 |> vars_poly) in
    RecordUpdateA (res, Some r)
  | TypeConstr (v, s), TypA ->
    let res = tallying_nonempty [(vartype v, s)] in
    ConstrA res
  | App (v1, v2), TypA ->
    let t1 = vartype v1 in
    let t2 = vartype v2 in
    let r1 = refresh_all (vars_poly t1) in
    let r2 = refresh_all (vars_poly t2) in
    let t1 = Subst.apply r1 t1 in
    let t2 = Subst.apply r2 t2 in
    let alpha = TVar.mk_poly None in
    let arrow_type = mk_arrow (cons t2) (TVar.typ alpha |> cons) in
    log ~level:4 "@.Approximate tallying for %a: %a <= %a@."
      Variable.pp vardef pp_typ t1 pp_typ arrow_type ;
    let res = approximate_app false t1 t2 alpha in
    let res = simplify_tallying (TVar.typ alpha) res in
    let (s1, s2) = res |> List.map (fun s ->
      (Subst.compose_restr s r1, Subst.compose_restr s r2)
    ) |> List.split in
    AppA (s1, s2)
  | Ite (v, s, _, _), TypA ->
    let t = vartype v in
    if subtype t empty then EmptyA
    else if subtype t s then ThenA
    else if subtype t (neg s) then ElseA
    else assert false
  | Lambda (_, v, e), PartialAnnot.LambdaA (s, pannot) ->
    let env = Env.add v s env in
    let annot = infer_inst tenv env pannot e in
    LambdaA (s, annot)
  | _, _ ->  assert false

and infer_inst tenv env pannot e =
  let open PartialAnnot in
  let open FullAnnot in
  let vartype v = Env.find v env in
  match e, pannot with
  | e, PartialAnnot.Inter i ->
    Inter (infer_inst_inter (fun pannot -> infer_inst tenv env pannot e) i)
  | Var v, Typ ->
    let r = refresh_all (vartype v |> vars_poly) in
    BVar r
  | Bind (_, _, e), PartialAnnot.Skip pannot ->
    let annot = infer_inst tenv env pannot e in
    FullAnnot.Skip annot
  | Bind (v, a, e), PartialAnnot.Keep (pannot_a, branches) ->
    assert (branches <> []) ;
    let annot_a = infer_inst_a v tenv env pannot_a a in
    let t = typeof_a_nofail v tenv env annot_a a in
    let (branches, inst) = List.fold_left
      (fun (branches, inst) br ->
      match br with
      | SExpl (si, pannot) ->
        let t = cap_o t si in
        let env = Env.add v t env in
        ((si, infer_inst tenv env pannot e)::branches, inst)
      | SUnr si ->
        let t = cap_o t si in
        let sol = tallying_one [(t, empty)] in
        (branches, sol::inst)
      | _ -> assert false
    ) ([], []) branches in
    FullAnnot.Keep (annot_a,
      (branches, Utils.remove_duplicates Subst.equiv inst))
  | _, _ ->  assert false

(* ====================================== *)
(* =============== INFER B ============== *)
(* ====================================== *)

(* TODO: Stop trying to use the same type variables in the tallying instances
   (this would avoid having to rename monomorphic variables when exiting a lambda) *)

type 'a res =
  | Ok of 'a
  | Split of Env.t * 'a * 'a
  | Subst of (Subst.t * 'a) list
  | NeedVar of VarSet.t * 'a * 'a

let map_res f res =
  match res with
  | Ok a -> Ok (f a)
  | Split (env, a1, a2) ->
    Split (env, f a1, f a2)
  | Subst lst ->
    Subst (lst |> List.map (fun (s, a) -> (s, f a)))
  | NeedVar (vs, a1, a2) -> NeedVar (vs, f a1, f a2)

let needvar env vs a1 a2 =
  let vs = VarSet.of_list vs in
  let vs = VarSet.diff vs (Env.domain env |> VarSet.of_list) in
  NeedVar (vs, a1, a2)

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
  | Subst [(subst, pannot)] when Subst.is_identity subst -> Some pannot
  | NeedVar (vs, pannot, _) when VarSet.is_empty vs -> Some pannot
  | _ -> None

let subst_more_general tvars s1 s2 =
  let s2m = Subst.codom s2 |> monomorphize in
  let s1g = TVarSet.diff (Subst.codom s1) tvars |> generalize in
  Subst.destruct s1 |> List.map (fun (v,t1) ->
    let t2 = Subst.find' s2 v in
    let t2 = Subst.apply s2m t2 in
    let t1 = Subst.apply s1g t1 in
    [(t1, t2) ; (t2, t1)]
  ) |> List.flatten |> tallying <> []

let res_var = TVar.mk_mono None
let simplify_tallying_infer env res sols =
  let tvars = Env.tvars env |> TVarSet.filter TVar.is_mono in
  let params_types = Env.domain env |>
    List.filter Variable.is_lambda_var |>
    List.map (fun v -> Env.find v env)
  in
  let mono_vars sol =
    let sol = Subst.restrict sol tvars in
    TVarSet.union (Subst.codom sol) tvars
  in
  let nb_new_vars sol =
    let nv = TVarSet.diff (mono_vars sol) tvars in
    nv |> TVarSet.destruct |> List.length
  in
  let better_sol sol1 sol2 =
    nb_new_vars sol1 <= nb_new_vars sol2 &&
    subst_more_general TVarSet.empty sol1 sol2
  in
  let try_simplify sol v t =
    let pvs = TVarSet.diff (vars t) tvars in
    let g = generalize pvs in let m = Subst.inverse_renaming g in
    let t = Subst.apply g t in
    let res = tallying [(TVar.typ v, t) ; (t, TVar.typ v)]
    |> List.map (fun s ->
      let s = Subst.compose_restr s g in
      let s = Subst.compose_restr m s in
      let mono_subst = monomorphize (Subst.codom s) in
      Subst.compose_restr mono_subst s
    )
    |> List.filter (fun s ->
      let res = Subst.find' sol res_var in
      let res' = Subst.apply s res in
      let g = vars res' |> generalize in
      let res' = Subst.apply g res' in
      subtype_poly res' res
    )
    in
    match res with
    | [] -> None
    | sol::_ -> Some sol
  in
  let merge_on_domain merge dom lst =
    dom |> List.map (fun v ->
      let t = lst |> List.map (fun s -> Subst.find' s v) |> merge in
      (v, t)
    ) |> Subst.construct
  in
  sols
  (* Restrict to tvars and store result *)
  |> List.map (fun sol ->
    let res = Subst.apply sol res in
    let sol = Subst.restrict sol tvars in
    Subst.combine sol (Subst.construct [(res_var, res)])
  )
  (* Generalize vars in the result when possible *)
  |> List.map (fun sol ->
    let tvars' = mono_vars sol in
    let res = Subst.find' sol res_var in
    let g = generalize (TVarSet.diff (vars res) tvars') in
    let res = Subst.apply g res in
    let clean = clean_type_subst ~pos:empty ~neg:any res in
    let g = Subst.compose_restr clean g in
    Subst.compose g sol
  )
  (* Remove solutions that require "undesirable" lambda branches *)
  |> List.filter (fun sol ->
    params_types |> List.for_all (fun t ->
      TVarSet.inter (vars_mono t) (Subst.dom sol) |> TVarSet.is_empty ||
      is_undesirable t || not (is_undesirable (Subst.apply sol t))
    )
  )
  (* Simplify (light) *)
  |> List.map (fun sol ->
    let new_dom = TVarSet.inter (Subst.dom sol) tvars in
    List.fold_left (fun sol v ->
      let t = Subst.find' sol v in
      (* let v = TVar.mk_fresh v in *)
      (* NOTE: we allow to rename mono vars even if already in the env...
         this might create an uneeded correlation but it simplifies a lot. *)
      let vs = (*TVarSet.diff (top_vars t) tvars*) top_vars t in
      let s = replace_vars t vs v in
      Subst.compose s sol
    ) sol (new_dom |> TVarSet.destruct)
  )
  (* Merge substitutions when possible *)
  |> regroup_equiv (fun s1 s2 ->
    let s1 = Subst.restrict s1 tvars in
    let s2 = Subst.restrict s2 tvars in
    Subst.equiv s1 s2
    )
  |> List.map (fun to_merge ->
    let common = Subst.restrict (List.hd to_merge) tvars in
    (* conj instead of conj_o, because in some cases it can be very complex types
       without being used later (e.g. when there is no tvar to infer) *)
    let respart = merge_on_domain conj [res_var] to_merge in
    Subst.combine common respart
  )
  (* Simplify (heavy) *)
  |> List.map (fun sol ->
    let new_dom = TVarSet.inter (Subst.dom sol) tvars in
    List.fold_left (fun sol v ->
      let t = Subst.find' sol v in
      match try_simplify sol v t with
      | None -> sol
      | Some s -> Subst.compose s sol
    ) sol (new_dom |> TVarSet.destruct)
  )
  (* Remove "less general" solutions *)
  |> keep_only_minimal better_sol
  (* Restrict and remove duplicates *)
  |> List.map (fun sol -> Subst.restrict sol tvars)
  |> remove_duplicates Subst.equiv
  (* Printing (debug) *)
  (* |> (fun res ->
    Format.printf "=== Solutions ===@." ;
    Format.printf "with tvars=%a@." TVarSet.pp tvars ;
    res |> List.iter (fun s -> Format.printf "%a@." Subst.pp s) ;
    res
  ) *)

let estimate_inter estimate_branch (lst1, lst2, _) =
  let lst = lst1@lst2 |> List.filter_map (fun (pannot, _, _) ->
    estimate_branch pannot
  ) in
  if lst = [] then None
  else Some (conj_o lst)

let rec estimate_branch_a env a pannot_a =
  (* TODO: refine this function so the branch taken by a typecase matters ?
     (we could associate a symbolic typevar to each binding and type them with
     this typevar instead of Any) *)
  let open PartialAnnot in
  match a, pannot_a with
  | _, UntypA -> None
  | _, TypA -> Some any
  | _, InferA -> Some any
  | _, InterA i -> estimate_inter (estimate_branch_a env a) i
  | Lambda (_, v, e), LambdaA (s, pannot) ->
    let env = Env.add v s env in
    estimate_branch env e pannot |> Option.map (fun t ->
      mk_arrow (cons s) (cons t)
      (* NOTE: the estimation below reduces the number of branches a lot,
         though in some cases it could prune important branches. *)
      (* mk_arrow (cons s) any_node *)
    )
  | _, _ -> assert false

and estimate_branch env e pannot =
  let open PartialAnnot in
  let estimate_splits v t e splits =
    let splits =
      splits |> List.map (function
          SExpl (s, pannot)
        | SProp (s, pannot)
        | SInfer (s, pannot) ->
          let env = Env.add v (cap_o t s) env in
          estimate_branch env e pannot
        | SUnr _ -> Some empty
      ) in
    if List.mem None splits then None
    else Some (List.map Option.get splits |> disj_o)
  in
  match e, pannot with
  | _, Untyp -> None
  | _, Inter i -> estimate_inter (estimate_branch env e) i
  | Var v, _ when Env.mem v env -> Some (Env.find v env)
  | Var _, _ -> None
  | Bind (v, _, e), Skip pannot ->
    let env = Env.add v any env in
    estimate_branch env e pannot
  | Bind (v, a, e), Keep (pannot_a, splits) ->
    let t = estimate_branch_a env a pannot_a |> Option.get in
    estimate_splits v t e splits
  | Bind (v, a, e), TryKeep (pannot_a, pannot1, pannot2) ->
    begin match estimate_branch_a env a pannot_a with
    | None -> estimate_branch env e pannot2
    | Some t ->
      let env = Env.add v t env in
      estimate_branch env e pannot1
    end
  | _, _ -> assert false

(* TODO: adapt branch pruning to new system...
   i) estimations should not be updated even after the branch has been typed
   ii) intersections of size 1 should be removed
   iii) estimations of explored branches should be passed as arg when
   typing another branch, so that it can be considered when removing branches *)
let infer_branches_inter env infer_branch infer_inst
  typeof apply_subst_branch (b1, b2, tf) =
  let tvars = Env.tvars env in
  let tvars = TVarSet.filter TVar.is_mono tvars in
  let subtype_gen a b =
    let gen = TVarSet.diff (vars a) tvars |> generalize in
    let a = Subst.apply gen a in
    subtype_poly a b
  in
  if b1 = [] && b2 = [] then Subst []
  else begin
    let uNb = List.length b2 and eNb = List.length b1 in
    let nontrivial = uNb + eNb > 1 in
    if nontrivial then begin
      log ~level:0 "Typing intersection with %n unexplored branches (and %n explored).@."
        uNb eNb ;
      (* if uNb >= 5 then
        b2@b3 |> List.iter (fun (_,_,est) -> Format.printf "Est: %a@." pp_typ est) *)
    end ;
    let rec aux explored pending =
      let smg = subst_more_general tvars in
      let leq s s' = (smg s s' |> not) || smg s' s in
      let leq (_,s,_) (_,s',_) = leq s s' in
      let more_specific s s' = smg s' s && not (smg s s') in
      let rm_useless explored pending lst =
        lst |> Utils.filter_among_others (fun (_,s,est) others ->
          let leqs = others@pending |> List.filter (fun (_,s',_) -> more_specific s' s) in
          let leqs = leqs@explored in
          let t_est = leqs |> List.map Utils.trd3 |> conj in
          leqs = [] || (subtype_gen t_est est |> not)
        )
      in
      (* Remove branches that are estimated not to add anything *)
      let pending = rm_useless explored [] pending in
      match pending with
      | [] ->
        let explored =
          if tf || List.length explored <= 1 then explored
          else
            (* When we just finished typing the intersection, we rename the type vars
               of the branches so that they are independant, and we remove redundant branches *)
            explored
            |> List.map (fun (pannot, s, est) ->
              let new_vars = TVarSet.diff (vars_mono est) tvars in
              let subst = refresh_all new_vars in
              (apply_subst_branch subst pannot, Subst.compose_restr subst s,
              Subst.apply subst est)
            )
            |> Utils.filter_among_others
            (fun (_,_,est) others ->
              let est' = others |> List.map Utils.trd3 |> conj in
              subtype_gen est' est |> not
            )
        in
        Ok (explored, [], true)
      | pending ->
        let f br others = others |> List.for_all (leq br) in
        (* Select more specific branches first *)
        let ((pannot, s, est), pending) = find_among_others f pending |> Option.get in
        if nontrivial then
          log ~level:3 "Exploring intersection issued from %a@." Subst.pp s;
        begin match infer_branch pannot with
        | Ok pannot ->
          let annot = infer_inst pannot in
          let est' = typeof annot in
          (* if nontrivial
            && env |> Env.domain |> List.exists (Variable.is_lambda_var) |> not
          then begin
            Format.printf "======================@." ;
            Format.printf "Branch typed: %a@." pp_typ est' ;
            Format.printf "Former est: %a@." pp_typ est ;
            Format.printf "From subst: %a@." Subst.pp s ;
            Format.printf "Env domain: %a@." (Utils.pp_list Variable.pp) (Env.domain env) ;
            Format.printf "Env: %a@." Env.pp (Env.filter (fun v _ ->
              Variable.is_lambda_var v) env)
          end ; *)
          (* If the type of this new branch does not add anything, remove it *)
          let explored =
            if explored = [] then (pannot, s, est')::explored
            else
              let t = List.map Utils.trd3 explored |> conj in
              if subtype_gen t est' then explored
              else (pannot, s, est')::explored
          in
          aux explored pending
        | res -> map_res (fun x -> (explored, (x,s,est)::pending, tf)) res
        end
    in
    (* NOTE: branches already typed are not typed again. *)
    aux b1 b2
  end

let filter_refinement env env' =
  Env.filter (fun v t -> subtype (Env.find v env) t |> not) env'

let normalize_subst env apply_subst_branch estimate_branch mk_inter res =
  let tvars = Env.tvars env in
  match res with
  | Subst lst ->
    let sigma = lst |>
      List.map (fun (subst,_) -> Subst.restrict subst tvars) in
    let sigma = (Subst.identity)::sigma in
    let sigma = remove_duplicates Subst.equiv sigma in
    let res = sigma |> List.map (fun subst ->
      let bs =
        lst |> List.filter_map (fun (subst', pannot) ->
          let subst_cur = Subst.remove subst' tvars in
          let subst' = Subst.restrict subst' tvars in
          if Subst.equiv subst' subst
          then
            let pannot = apply_subst_branch subst_cur pannot in
            estimate_branch pannot |> Option.map
              (fun est -> (pannot, subst_cur, est))
          else None
        )
      in
      (subst, mk_inter [] bs false)
    ) in
    Subst res
  | res -> res

let rec infer_branches_a vardef tenv env pannot_a a =
  let memvar v = Env.mem v env in
  let vartype v = Env.find v env in
  let needvar = needvar env in
  let packannot a = List.map (fun s -> (s, a)) in
  let open PartialAnnot in
  match a, pannot_a with
  | a, InterA i ->
    infer_branches_inter
      env
      (fun pannot_a -> infer_branches_a_iterated vardef tenv env pannot_a a)
      (fun pannot_a -> infer_inst_a vardef tenv env pannot_a a)
      (fun annot_a -> typeof_a vardef tenv env annot_a a)
      apply_subst_a
      i
    |> map_res (fun x -> InterA x)
  | _, TypA -> Ok (TypA)
  | _, UntypA -> Subst []
  | Alias v, InferA when memvar v -> Ok (TypA)
  | Alias _, InferA -> Subst []
  | Abstract _, InferA | Const _, InferA -> Ok (TypA)
  | Pair (v1, v2), InferA | Let (v1, v2), InferA ->
    needvar [v1; v2] TypA UntypA
  | Projection (p, v), InferA ->
    if memvar v then
      let t = vartype v in
      let alpha = Variable.to_typevar vardef
        (* TVar.mk_mono (Some (Variable.show vardef)) *)
      in
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
      Subst (packannot TypA res)
    else
      needvar [v] InferA UntypA
  | RecordUpdate (v, _, None), InferA ->
    if memvar v then
      let res = tallying_infer [(vartype v, record_any)] in
      let res = simplify_tallying_infer env empty res in
      Subst (packannot TypA res)
    else
      needvar [v] InferA UntypA
  | RecordUpdate (v, _, Some v'), InferA ->
    if memvar v && memvar v' then
      let res = tallying_infer [(vartype v, record_any)] in
      let res = simplify_tallying_infer env empty res in
      Subst (packannot TypA res)
    else
      needvar [v ; v'] InferA UntypA
  | TypeConstr (v, s), InferA ->
    if memvar v then
      let res = tallying_infer [(vartype v, s)] in
      let res = simplify_tallying_infer env empty res in
      Subst (packannot TypA res)
    else
      needvar [v] InferA UntypA
  | App (v1, v2), InferA ->
    if memvar v1 && memvar v2 then
      let t1 = vartype v1 in
      let t2 = vartype v2 in
      let alpha = Variable.to_typevar vardef
        (* TVar.mk_mono (Some (Variable.show vardef)) *)
      in
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
      Subst (packannot TypA res)
    else
      needvar [v1;v2] InferA UntypA
  | Ite (v, tau, v1, v2), InferA ->
    if memvar v then
      let t = vartype v in
      let not_else = subtype t tau in
      let not_then = subtype t (neg tau) in
      if not_then && not_else then Ok TypA        
      else if not_then then needvar [v2] TypA UntypA
      else if not_else then needvar [v1] TypA UntypA
      else Split (Env.singleton v tau, InferA, InferA)
    else needvar [v] InferA UntypA
  | Lambda (Unnanoted, _, _), InferA ->
    let alpha = Variable.to_typevar vardef |> TVar.typ
      (* TVar.mk_mono (Some (Variable.show vardef)) |> TVar.typ *)
    in
    let pannot_a = LambdaA (alpha, Infer) in
    infer_branches_a vardef tenv env pannot_a a
  | Lambda (ADomain ts, _, _), InferA ->
    let alpha = Variable.to_typevar vardef
      (* TVar.mk_mono (Some (Variable.show vardef)) *)
    in
    let pannot_a = LambdaA (TVar.typ alpha, Infer) in
    let lst = ts |> List.map (fun t ->
      ([(alpha,t)] |> Subst.construct, pannot_a)
    ) in
    Subst lst
  | Lambda (_, v, e), LambdaA (s, pannot) ->
    log ~level:2 "Entering lambda for %a with domain %a.@." Variable.pp v pp_typ s ;
    if is_empty s then Subst []
    else
      let env = Env.add v s env in
      infer_branches_iterated tenv env pannot e
      |> map_res (fun x -> LambdaA (s, x))
  | _, _ -> assert false

and infer_branches_union tenv env v a e t splits =
  let packannot a = List.map (fun s -> (s, a)) in
  let open PartialAnnot in
  if List.for_all (function SUnr _ -> true | _ -> false) splits
  then
    infer_branches_union tenv env v a e t ((SExpl (empty, Infer))::splits)
  else
    let rec aux splits =
      match splits with
      | [] -> Ok []
      | (SInfer (s, pannot))::splits ->
        let t = cap_o t s in
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
        then aux ((SUnr s)::splits)
        else
          Subst ((packannot ((SUnr s)::splits) res)@
            [(Subst.identity, (SProp (s, pannot))::splits)])
      | (SProp (s, pannot))::splits ->
        let propagate =
          refine_a tenv env a (neg s)
          |> List.find_opt (is_compatible env)
        in
        begin match propagate with
        | Some env' ->
          log ~level:0 "Var %a is ok but a split must be propagated.@." Variable.pp v ;
          let env' = filter_refinement env env' in
          Split (env', (SUnr s)::splits, (SProp (s, pannot))::splits)
        | None -> aux ((SExpl (s, pannot))::splits)
        end
      | (SUnr s)::splits ->
        aux splits |> map_res (fun x -> (SUnr s)::x)
      | (SExpl (s, pannot))::splits ->
        log ~level:1 "Exploring split %a for %a.@." pp_typ s Variable.pp v ;
        let env' = Env.add v (cap_o t s) env in
        begin match infer_branches_iterated tenv env' pannot e with
        | Ok pannot ->
          aux splits |> map_res (fun x -> (SExpl (s, pannot))::x)
        | Split (env', pannot1, pannot2) when Env.mem v env' ->
          let s' = Env.find v env' in
          let splits1 = [ SInfer (cap_o s s' |> simplify_typ, pannot1) ;
                          SInfer (diff_o s s' |> simplify_typ, pannot2) ]@splits in
          let splits2 = [ SExpl (s,pannot2) ]@splits in
          Split (Env.rm v env', splits1, splits2)
        | res -> res |> map_res (fun x -> (SExpl (s, x))::splits)
        end
    in
    aux splits

and infer_branches tenv env pannot e =
  let needvar = needvar env in
  let open PartialAnnot in
  match e, pannot with
  | e, Inter i ->
    infer_branches_inter
      env
      (fun pannot -> infer_branches_iterated tenv env pannot e)
      (fun pannot -> infer_inst tenv env pannot e)
      (fun annot -> typeof tenv env annot e)
      apply_subst
      i
    |> map_res (fun x -> Inter x)
  | Var _, Typ -> Ok Typ
  | Var _, Untyp -> Subst []
  | Var v, Infer -> needvar [v] Typ Untyp
  | Bind _, Infer -> infer_branches tenv env (Skip Infer) e
  | Bind (v, _, e), Skip pannot ->
    begin match infer_branches_iterated tenv env pannot e with
    | NeedVar (vs, pannot1, pannot2) when VarSet.mem v vs ->
      log ~level:0 "Var %a needed.@." Variable.pp v ;
      let pannot1 = TryKeep (InferA, pannot1, pannot2) in
      let pannot2 = Skip pannot2 in
      NeedVar (VarSet.remove v vs, pannot1, pannot2)
    | res -> map_res (fun x -> Skip x) res
    end
  | Bind (v, a, _), TryKeep (pannot_a, pannot1, pannot2) ->
    log ~level:1 "Trying to type var %a.@." Variable.pp v ;
    begin match infer_branches_a_iterated v tenv env pannot_a a with
    | Ok pannot_a ->
      infer_branches tenv env (Keep (pannot_a, [SExpl (any, pannot1)])) e
    | Subst lst when
      List.for_all (fun (s,_) -> Subst.is_identity s |> not) lst ->
      let lst = lst |> List.map (fun (s, pannot_a) ->
        (s, TryKeep (pannot_a, pannot1, pannot2))
      ) in
      Subst (lst@[(Subst.identity, Skip pannot2)])
    | res -> map_res (fun x -> TryKeep (x, pannot1, pannot2)) res
    end
  | Bind (v, a, e), Keep (pannot_a, splits) ->
    log ~level:1 "Inferring var %a.@." Variable.pp v ;
    assert (splits <> []) ;
    (* NOTE: The call to infer_branches_a_iterated should return Ok most of time,
       it could probably be optimized away. *)
    begin match infer_branches_a_iterated v tenv env pannot_a a with
    | Ok pannot_a ->
      let annot_a = infer_inst_a v tenv env pannot_a a in
      let t = typeof_a_nofail v tenv env annot_a a in
      log ~level:1 "Var %a typed with type %a.@." Variable.pp v pp_typ t ;
      (* If the definition is a function whose DNF has many disjuncts,
         we try to split them. *)
      let propagate =
        let dnf = dnf t |> simplify_dnf in
        if subtype t arrow_any && List.length dnf >= 2 then
          dnf |> simplify_dnf |> Utils.map_among_others' (fun _ others ->
            let s = others |> List.map branch_type |> List.map bot_instance
              |> disj in
            let mono = monomorphize (vars_poly s) in
            let s = Subst.apply mono s in
            refine_a tenv env a s
          )
          |> List.flatten
          |> List.find_opt (is_compatible env)
        else None
      in
      begin match propagate with
      | Some env' ->
        log ~level:1 "Var %a is ok but its DNF needs a split.@." Variable.pp v ;
        let env' = filter_refinement env env' in
        Split (env', Keep (pannot_a, splits), Keep (pannot_a, splits))
      | None ->
        (* Now, we perform the splits from the annotations *)
        log ~level:2 "Typing body for %a with splits %a.@."
          Variable.pp v (pp_list pp_typ) (effective_splits splits) ;
        infer_branches_union tenv env v a e t splits
        |> map_res (fun x -> Keep (pannot_a, x))
      end
    | res -> res |> map_res (fun x -> Keep (x, splits))
    end
  | _, _ -> assert false

and infer_branches_a_iterated vardef tenv env pannot_a a =
  log ~level:5 "infer_branches_a_iterated@." ;
  let res = infer_branches_a vardef tenv env pannot_a a in
  match should_iterate res with
  | None -> normalize_subst env
      PartialAnnot.apply_subst_a (estimate_branch_a env a)
      (fun a b c -> PartialAnnot.InterA (a,b,c)) res
  | Some pannot_a -> infer_branches_a_iterated vardef tenv env pannot_a a

and infer_branches_iterated tenv env pannot e =
  log ~level:5 "infer_branches_iterated@." ;
  let res = infer_branches tenv env pannot e in
  match should_iterate res with
  | None -> normalize_subst env
      PartialAnnot.apply_subst (estimate_branch env e)
      (fun a b c -> PartialAnnot.Inter (a,b,c)) res
  | Some pannot -> infer_branches_iterated tenv env pannot e

(* ====================================== *)
(* ================ INFER =============== *)
(* ====================================== *)

let infer tenv env e =
  let open PartialAnnot in
  match infer_branches_iterated tenv env Infer e with
  | Subst [] -> raise (Untypeable ([], "Annotations inference failed."))
  | Ok annot -> infer_inst tenv env annot e
  | NeedVar (vs, _, _) ->
    Format.printf "NeedVar %a@." (pp_list Variable.pp) (VarSet.to_seq vs |> List.of_seq) ;
    assert false
  | Split (gamma, _, _) ->
    Format.printf "Split %a@." Env.pp gamma ;
    assert false
  | Subst lst ->
    (* Format.printf "Subst %a@." (pp_long_list Subst.pp) (List.map fst lst) ; *)
    Format.printf "Subst %a@."
      (pp_long_list TVarSet.pp) (List.map fst lst |> List.map Subst.dom) ;
    assert false

let typeof_simple tenv env e =
  let annot = infer tenv env e in
  typeof_nofail tenv env annot e
