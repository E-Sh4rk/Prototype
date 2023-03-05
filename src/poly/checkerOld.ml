open Types.Base
open Types.Tvar
open Types.Additions
open Common
open Parsing.Variable
open Msc
open AnnotationsOld
open Utils

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
  else raise (Untypeable (pos, "Invalid branch: a branch should be monomorphic."))

let check_novar pos t =
  if is_novar_typ t
    then ()
    else raise (Untypeable (pos, "Invalid split: a split shouldn't contain type variables."))  

let rename_check pos r t =
  if Subst.is_renaming r &&
    Subst.dom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty &&
    Subst.codom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty
  then Subst.apply r t
  else raise (Untypeable (pos, "Invalid renaming."))

let generalize_check pos env r t =
  if Subst.is_renaming r &&
    Subst.dom r |> TVarSet.filter TVar.is_poly |> TVarSet.is_empty &&
    Subst.codom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty &&
    Subst.dom r |> TVarSet.inter (Env.tvars env) |> TVarSet.is_empty
  then Subst.apply r t
  else raise (Untypeable (pos, "Invalid generalization."))  

(* TODO: test examples in flatten.ml, and merge them with test.ml *)
let rec typeof_a vardef tenv env annot_a a =
  let open FullAnnot in
  let pos = Variable.get_locations vardef in
  let var_type v = var_type v env in
  let rename_check = rename_check pos in
  let instantiate_check = instantiate_check pos in
  let check_mono = check_mono pos in
  let untypeable str = raise (Untypeable (pos, str)) in
  let type_lambda env annot v e =
    if annot = []
    then untypeable ("Invalid lambda: there must be at least 1 branch.")
    else
      let branches =
          annot |> List.map (fun (group, gen) ->
            let (doms, codoms) =
              group |> List.map (fun (s, annot) ->
                check_mono s ;
                let env = Env.add v s env in
                let t = typeof tenv env annot e in
                (s,t)
              ) |> List.split
            in
            let (dom, codom) = (disj_o doms, disj_o codoms) in
            mk_arrow (cons dom) (cons codom)
            |> generalize_check pos env gen
        ) in
      branches |> conj_o
  in
  begin match a, annot_a with
  | Alias v, AliasA -> var_type v
  | Const c, ConstA -> typeof_const_atom tenv c
  | Abstract t, AbstractA gen -> generalize_check pos env gen t
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
  | Ite (v, _, _, _), EmptyA ss ->
    let t = var_type v |> instantiate_check ss in
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
  | Lambda (_, v, e), LambdaA branches -> type_lambda env branches v e
  | _, _ -> untypeable ("Invalid annotations.")
  end
  |> bot_instance |> simplify_typ
  
and typeof tenv env annot e =
  let open FullAnnot in
  begin match e, annot with
  | Var v, BVar r -> var_type v env |> rename_check [] r
  | Bind (v, a, e), Keep (annot_a, ty, splits) ->
    let t = (* NOTE: ty different than None bypasses type checking. *)
      begin match ty with
      | None -> typeof_a v tenv env annot_a a
      | Some t -> t
      end in
    let pos = Variable.get_locations v in
    let untypeable str = raise (Untypeable (pos, str)) in
    if splits = []
    then untypeable ("Invalid decomposition: cannot be empty.")
    else
      if subtype t (splits |> List.map fst |> disj)
      then
        splits |> List.map (fun (s, annot) ->
          check_novar pos s ;
          let env = Env.add v (cap t s) env in
          typeof tenv env annot e
        ) |> disj_o
      else untypeable ("Invalid decomposition: does not cover the whole domain.")
  | Bind (v, _, e), Skip annot ->
    assert (Env.mem v env |> not) ;
    typeof tenv env annot e
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
    let dnf = Env.find v1 env |> dnf |> simplify_dnf in
    let singl = List.length dnf <= 1 in
    dnf |> List.map (fun lst ->
      let ti = branch_type lst in
      let alpha = TVar.mk_poly None in
      let constr = [ (ti, mk_arrow (TVar.typ alpha |> cons) (cons t)) ] in
      let res = tallying constr in
      res |> List.map (fun sol ->
        let ti = apply_subst_simplify sol ti in
        let argt = Subst.find' sol alpha in
        let clean_subst =  clean_type_subst ~pos:any ~neg:empty argt in
        let ti = Subst.apply clean_subst ti in
        let argt = Subst.apply clean_subst argt in
        let clean_subst =  clean_type_subst ~pos:any ~neg:empty ti in
        let ti = Subst.apply clean_subst ti |> ground_inf in
        let argt = Subst.apply clean_subst argt |> ground_inf in
        if singl then Env.singleton v2 argt (* Optimisation *)
        else Env.construct_dup [ (v1, ti) ; (v2, argt) ]
      )
    ) |> List.flatten
    (* |> List.filter (fun env -> env |> Env.tvars |> TVarSet.is_empty) *)
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

let types_equiv_modulo_renaming mono t1 t2 =
  let (v1s, v2s) = (TVarSet.diff (vars t1) mono, TVarSet.diff (vars t2) mono) in
  let (v1s, v2s) = (TVarSet.diff v1s v2s, TVarSet.diff v2s v1s) in
  let (v1s, v2s) = (TVarSet.destruct v1s, TVarSet.destruct v2s) in
  if List.length v1s <> List.length v2s
  then None
  else
    perm v2s |> List.find_map (fun v2s ->
      let subst = List.map2 (fun v1 v2 ->
        (v1, TVar.typ v2)
        ) v1s v2s |> Subst.construct in
        let t1 = Subst.apply subst t1 in
        if equiv t1 t2 then Some subst else None 
    )

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

let rec infer_inst_a vardef tenv env pannot_a a =
  let open PartialAnnot in
  let open FullAnnot in
  let vartype v = Env.find v env in
  match a, pannot_a with
  | Alias _, PartialA -> AliasA
  | Const _, PartialA -> ConstA
  | Let _, PartialA -> LetA
  | Abstract t, PartialA ->
    let gvars = TVarSet.diff (vars_mono t) (Env.tvars env) in
    AbstractA (generalize gvars)
  | Pair (v1, v2), PartialA ->
    let r1 = refresh_all (vartype v1 |> vars_poly) in
    let r2 = refresh_all (vartype v2 |> vars_poly) in
    PairA (r1, r2)
  | Projection (p, v), PartialA ->
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
  | RecordUpdate (v, _, None), PartialA ->
    let res = tallying_nonempty [(vartype v, record_any)] in
    let res = simplify_tallying record_any res in
    RecordUpdateA (res, None)
  | RecordUpdate (v, _, Some v2), PartialA ->
    let res = tallying_nonempty [(vartype v, record_any)] in
    let res = simplify_tallying record_any res in
    let r = refresh_all (vartype v2 |> vars_poly) in
    RecordUpdateA (res, Some r)
  | TypeConstr (v, s), PartialA ->
    let res = tallying_nonempty [(vartype v, s)] in
    ConstrA res
  | App (v1, v2), PartialA ->
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
  | Ite (v, s, _, _), PartialA ->
    let t = vartype v in
    let res = tallying [(t, empty)] in
    if res <> [] then EmptyA res
    else if subtype t s then ThenA
    else if subtype t (neg s) then ElseA
    else assert false
  | Lambda (_, v, e), PartialAnnot.LambdaA (b1, b2) ->
    assert (b2 = []) ;
    let branches = b1 |> List.map (fun group ->
      let group =
        group |> List.map (fun (s, pannot) ->
          let env = Env.add v s env in
          let annot = infer_inst tenv env pannot e in
          (s, annot)
        )
      in
      let gvars = group |> List.map fst |> List.map vars_mono |> TVarSet.union_many in
      let gvars = TVarSet.diff gvars (Env.tvars env) in
      (group, generalize gvars)
    ) in
    FullAnnot.LambdaA branches
  | _, _ ->  assert false

and infer_inst tenv env pannot e =
  let open PartialAnnot in
  let open FullAnnot in
  let vartype v = Env.find v env in
  match e, pannot with
  | Var v, Partial ->
    let r = refresh_all (vartype v |> vars_poly) in
    BVar r
  | Bind (_, _, e), PartialAnnot.Skip pannot ->
    let annot = infer_inst tenv env pannot e in
    FullAnnot.Skip annot
  | Bind (v, a, e), PartialAnnot.Keep (pannot_a, branches) ->
    let annot_a = infer_inst_a v tenv env pannot_a a in
    let t = typeof_a_nofail v tenv env annot_a a in
    let branches = branches |> List.map (fun (si, pannot) ->
      let t = cap_o t si in
      let env = Env.add v t env in
      (si, infer_inst tenv env pannot e)
    ) in
    FullAnnot.Keep (annot_a, None, branches)
  | _, _ ->  assert false

(* ====================================== *)
(* =============== INFER B ============== *)
(* ====================================== *)

type 'a res =
  | Ok of 'a
  | Split of Env.t * 'a * 'a
  | Subst of (Subst.t * 'a) list
  | NeedVar of (VarSet.t * 'a * 'a option)

let map_res f res =
  match res with
  | Ok a -> Ok (f a)
  | Split (env, a1, a2) ->
    Split (env, f a1, f a2)
  | Subst lst ->
    Subst (lst |> List.map (fun (s, a) -> (s, f a)))
  | NeedVar (vs, a, ao) ->
    NeedVar (vs, f a, Option.map f ao)

let needvar env vs a =
  let vs = VarSet.of_list vs in
  let vs = VarSet.diff vs (Env.domain env |> VarSet.of_list) in
  NeedVar (vs, a, None)

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

let subst_more_general s1 s2 =
  let s2m = Subst.codom s2 |> monomorphize in
  let s1g = Subst.codom s1 |> generalize in
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
    subst_more_general sol1 sol2
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
      let s = replace_vars t (TVarSet.diff (top_vars t) tvars) v in
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

let insert_new_branch tenv env x e groups branch =
  let type_branch (s, pannot) =
    let env = Env.add x s env in
    let annot = infer_inst tenv env pannot e in
    let t = typeof_nofail tenv env annot e in
    (s, t, (s, pannot))
  in
  let groups = groups |> List.map (fun branches ->
      let (ds, rs, branches) =
        branches |> List.map type_branch |> Utils.split3
      in
      let (d, r) = (disj ds, disj rs) in
      let t = mk_arrow (cons d) (cons r) in
      (t, d, r, branches)
    )
  in
  let (d, r, branch) = type_branch branch in
  let t = mk_arrow (cons d) (cons r) in
  let subtype_gen a b =
    let gen = TVarSet.diff (vars a) (Env.tvars env) |> generalize in
    let a = Subst.apply gen a in
    subtype_poly a b
  in
  let last4 (_,_,_,e) = e in
  if groups |> List.exists (fun (t',_,_,_) -> subtype_gen t' t)
  then
    (* Don't insert the branch if it does not strictly strengthen the groups *)
    List.map last4 groups
  else
    (* Insert the branch, but inside a group if possible *)
    let can_be_merged_in (t',d',r',_) _ =
      let dom = cup d d' in
      let codom = cup r r' in
      let nt = mk_arrow (cons dom) (cons codom) in
      subtype_gen nt t && subtype_gen nt t'
    in
    match Utils.find_among_others can_be_merged_in groups with
    | None -> [branch]::(List.map last4 groups)
    | Some ((_,_,_,group),groups) ->
      (branch::group)::(List.map last4 groups)

let rec infer_branches_a vardef tenv env pannot_a a =
  let memvar v = Env.mem v env in
  let vartype v = Env.find v env in
  let needvar = needvar env in
  let packannot a = List.map (fun s -> (s, a)) in
  let open PartialAnnot in
  let lambda v (b1, b2) e =
    log ~level:2 "Typing lambda for %a with unexplored branches %a.@."
      Variable.pp v (pp_list pp_typ) (List.map fst b2) ;
    let rec aux explored b =
      let explored_domain = explored |> disj in
      (* Remove branches with a domain that has already been explored *)
      let b = b |> List.filter
        (fun (s,_) -> subtype s explored_domain |> not) in
      match b with
      | [] -> Ok ([], [])
      | b ->
        let f (s, _) others = others |> List.for_all
          (fun (s', _) -> (subtype s' s |> not) || subtype s s')
        in
        let ((s, pannot), b) = find_among_others f b |> Option.get in
        log ~level:1 "Exploring lambda branch %a for %a.@." pp_typ s Variable.pp v ;
        let env' = Env.add v s env in
        begin match infer_branches_iterated tenv env' pannot e with
        | Ok pannot ->
          aux (s::explored) b
          |> map_res (fun (b1, b2) -> ((s, pannot)::b1, b2))
        | Subst lst ->
          let x = Env.tvars env in
          let sigma = lst |>
            List.map (fun (subst,_) -> Subst.restrict subst x) in
          let sigma = (Subst.identity)::sigma in
          let sigma = remove_duplicates Subst.equiv sigma in
          let res = sigma |> List.map (fun subst ->
            let b' =
              lst |> List.filter_map (fun (subst', pannot') ->
                let subst_cur = Subst.remove subst' x in
                let subst' = Subst.restrict subst' x in
                if Subst.equiv subst' subst
                then
                  let s = apply_subst_simplify subst_cur s in
                  let pannot' = apply_subst subst_cur pannot' in
                  (* If it is equivalent to an existing branch modulo renaming, don't add it. *)
                  let ts = (List.map fst b)@explored in
                  if ts |> List.exists (fun t -> types_equiv_modulo_renaming x s t <> None)
                  then None else Some (s, pannot')
                else None
              )
            in
            (subst, ([], b'@b))
          ) in
          Subst res
        | NeedVar (vs, pannot, None) ->
          NeedVar (vs, ([], (s, pannot)::b), Some ([], b))
        | res -> map_res (fun pannot -> ([], (s, pannot)::b)) res
        end
    in
    aux (b1 |> List.flatten |> List.map fst) b2 |>
      map_res (fun (b1', b2') ->
        let b1' = List.fold_left (insert_new_branch tenv env v e) b1 b1' in
        LambdaA (b1', b2')
      )
  in
  match a, pannot_a with
  | _, PartialA -> Ok (PartialA)
  | Alias v, InferA IMain when memvar v -> Ok (PartialA)
  | Alias _, InferA IMain -> Subst []
  | Abstract _, InferA IMain | Const _, InferA IMain -> Ok (PartialA)
  | Pair (v1, v2), InferA IMain | Let (v1, v2), InferA IMain ->
    needvar [v1; v2] PartialA
  | Projection (p, v), InferA IMain ->
    if memvar v then
      let t = vartype v in
      let alpha = Variable.to_typevar vardef in
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
      Subst (packannot PartialA res)
    else
      needvar [v] (InferA IMain)
  | RecordUpdate (v, _, None), InferA IMain ->
    if memvar v then
      let res = tallying_infer [(vartype v, record_any)] in
      let res = simplify_tallying_infer env empty res in
      Subst (packannot PartialA res)
    else
      needvar [v] (InferA IMain)
  | RecordUpdate (v, _, Some v'), InferA IMain ->
    if memvar v && memvar v' then
      let res = tallying_infer [(vartype v, record_any)] in
      let res = simplify_tallying_infer env empty res in
      Subst (packannot PartialA res)
    else
      needvar [v ; v'] (InferA IMain)
  | TypeConstr (v, s), InferA IMain ->
    if memvar v then
      let res = tallying_infer [(vartype v, s)] in
      let res = simplify_tallying_infer env empty res in
      Subst (packannot PartialA res)
    else
      needvar [v] (InferA IMain)
  | App (v1, v2), InferA IMain ->
    if memvar v1 && memvar v2 then
      let t1 = vartype v1 in
      let t2 = vartype v2 in
      let alpha = Variable.to_typevar vardef in
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
      Subst (packannot PartialA res)
    else
      needvar [v1;v2] (InferA IMain)
  | Ite (v, tau, _, _), InferA IMain ->
    if memvar v then
      let t = vartype v in
      let not_else = subtype t tau in
      let not_then = subtype t (neg tau) in
      if not_then || not_else then begin
        log ~level:3 "@.Tallying (inference) for %a: %a <= %a@."
          Variable.pp vardef pp_typ t pp_typ empty ;
        let res = tallying_infer [(t, empty)] in
        res |> List.iter (fun s ->
          log ~level:3 "Solution: %a@." Subst.pp s
        ) ;
        let res = simplify_tallying_infer env empty res in
        res |> List.iter (fun s ->
          log ~level:3 "Solution (simplified): %a@." Subst.pp s
        ) ;
        if List.exists Subst.is_identity res then
          Ok (PartialA)
        else if not_else then
          Subst ((packannot PartialA res)@[(Subst.identity, InferA IThen)])
        else
          Subst ((packannot PartialA res)@[(Subst.identity, InferA IElse)])
      end else
        Split (Env.singleton v tau, InferA IMain, InferA IMain)
    else
      needvar [v] (InferA IMain)
  | Ite (_, _, v1, _), InferA IThen -> needvar [v1] PartialA
  | Ite (_, _, _, v2), InferA IElse -> needvar [v2] PartialA
  | Lambda (Unnanoted, _, _), InferA IMain ->
    let alpha = Variable.to_typevar vardef in
    let pannot_a = LambdaA ([], [(TVar.typ alpha, Infer)]) in
    infer_branches_a vardef tenv env pannot_a a
  | Lambda (ADomain ts, _, _), InferA IMain ->
    let pannot_a = LambdaA ([], packannot Infer ts) in
    infer_branches_a vardef tenv env pannot_a a
  | Lambda (_, v, e), LambdaA (b1, b2) ->
    if (List.flatten b1)@b2 |> List.map fst |> disj |> is_empty
    then Subst [] else lambda v (b1,b2) e
  | _, _ -> assert false

and infer_branches_splits tenv env v a e t splits =
  if is_empty t
  then
    let (_, pannot) = List.hd splits in
    let env = Env.add v empty env in
    infer_branches_iterated tenv env pannot e
    |> map_res (fun pannot -> [(empty, pannot)])
  else
    let propagate =
      splits |> Utils.find_map_among_others (fun (s,_) others ->
        if subtype t s then None
        else
          refine_a tenv env a (neg s)
          |> List.find_opt (is_compatible env) |> Option.map (fun x -> (x, others))
      )
    in
    begin match propagate with
    | Some (env', splits') ->
      log ~level:1 "Var %a is ok but a split must be propagated.@." Variable.pp v ;
      let env' = Env.filter (fun v t -> subtype (Env.find v env) t |> not) env' in
      Split (env', splits', splits)
    | None ->
      log ~level:2 "Typing binding for %a with splits %a.@."
        Variable.pp v (pp_list pp_typ) (List.map fst splits) ;
      begin match splits with
      | [] -> Ok []
      | (s, pannot)::splits ->
        log ~level:1 "Exploring split %a for %a.@." pp_typ s Variable.pp v ;
        let env' = Env.add v (cap_o t s) env in
        begin match infer_branches_iterated tenv env' pannot e with
        | Ok pannot ->
          infer_branches_splits_iterated tenv env v a e t splits
          |> map_res (fun splits -> (s, pannot)::splits)
        | Split (env', pannot1, pannot2) when Env.mem v env' ->
          let s' = Env.find v env' in
          let splits1 = [ (cap_o s s', pannot1) ; (diff_o s s', pannot2) ]@splits in
          let splits2 = [ (s,pannot2) ]@splits in
          Split (Env.rm v env', splits1, splits2)
        | res -> res |> map_res (fun pannot -> (s, pannot)::splits)
        end  
      end
    end

and infer_branches tenv env pannot e =
  let needvar = needvar env in
  let open PartialAnnot in
  match e, pannot with
  | Var _, Partial -> Ok Partial
  | Var v, Infer -> needvar [v] Partial
  | Bind _, Infer -> infer_branches tenv env (Skip Infer) e
  | Bind (v, _, e), Skip pannot ->
    begin match infer_branches_iterated tenv env pannot e with
    | NeedVar (vs, pannot1, Some pannot2) when VarSet.mem v vs ->
      log ~level:0 "Var %a needed (optional).@." Variable.pp v ;
      let pannot1 = KeepSkip (InferA IMain, [(any, pannot1)], pannot2) in
      let pannot2 = Skip pannot2 in
      NeedVar (VarSet.remove v vs, pannot1, Some pannot2)
    | NeedVar (vs, pannot, None) when VarSet.mem v vs ->
      log ~level:0 "Var %a needed.@." Variable.pp v ;
      let pannot = Keep (InferA IMain, [(any, pannot)]) in
      NeedVar (VarSet.remove v vs, pannot, None)
    | res -> map_res (fun pannot -> Skip pannot) res
    end
  | Bind (v, a, _), KeepSkip (pannot_a, splits, pannot) ->
    log ~level:1 "Typing var %a (optional).@." Variable.pp v ;
    begin match infer_branches_a_iterated v tenv env pannot_a a with
    | Ok pannot_a -> infer_branches tenv env (Keep (pannot_a, splits)) e
    | Subst lst when
      List.for_all (fun (s,_) -> Subst.is_identity s |> not) lst ->
      let lst = lst |> List.map (fun (s, pannot_a) ->
        (s, KeepSkip (pannot_a, splits, pannot))
      ) in
      Subst (lst@[(Subst.identity, Skip pannot)])
    | NeedVar (vs, pannot_a, None) ->
      NeedVar (vs, KeepSkip (pannot_a, splits, pannot), Some (Skip pannot))
    | res -> map_res (fun pannot_a -> KeepSkip (pannot_a, splits, pannot)) res
    end
  | Bind (v, a, e), Keep (pannot_a, splits) ->
    log ~level:1 "Inferring var %a.@." Variable.pp v ;
    assert (splits <> []) ;
    begin match infer_branches_a_iterated v tenv env pannot_a a with
    | Ok pannot_a ->
      let annot_a = infer_inst_a v tenv env pannot_a a in
      let t = typeof_a_nofail v tenv env annot_a a in
      log ~level:1 "Var %a typed with type %a.@." Variable.pp v pp_typ t ;
      infer_branches_splits_iterated tenv env v a e t splits
      |> map_res (fun splits -> Keep (pannot_a, splits))
    | res -> res |> map_res (fun pannot_a -> Keep (pannot_a, splits))
    end
  | _, _ -> assert false

and infer_branches_a_iterated vardef tenv env pannot_a a =
  log ~level:5 "infer_branches_a_iterated@." ;
  let res = infer_branches_a vardef tenv env pannot_a a in
  match should_iterate res with
  | None -> res
  | Some pannot_a -> infer_branches_a_iterated vardef tenv env pannot_a a

and infer_branches_splits_iterated tenv env v a e t splits =
  log ~level:5 "infer_branches_splits_iterated@." ;
  let res = infer_branches_splits tenv env v a e t splits in
  match should_iterate res with
  | None -> res
  | Some splits -> infer_branches_splits tenv env v a e t splits

and infer_branches_iterated tenv env pannot e =
  log ~level:5 "infer_branches_iterated@." ;
  let res = infer_branches tenv env pannot e in
  match should_iterate res with
  | None -> res
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
