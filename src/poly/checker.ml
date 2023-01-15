module PMsc = Msc
open Types.Base
open Types.Tvar
open Types.Additions
open Common
open Parsing.Variable
open Msc
open Annotations
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
  else raise (Untypeable (pos, "Invalid branch: abstracted variable should be monomorphic."))

let rename_check pos r t =
  if Subst.is_renaming r &&
    Subst.dom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty &&
    Subst.codom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty
  then Subst.apply r t
  else raise (Untypeable (pos, "Invalid renaming."))

let generalize_check pos r t =
  if Subst.is_renaming r &&
    Subst.dom r |> TVarSet.filter TVar.is_poly |> TVarSet.is_empty &&
    Subst.codom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty
  then Subst.apply r t
  else raise (Untypeable (pos, "Invalid generalization."))  
  
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
        annot |> List.map (fun (s, annot) ->
          check_mono s ;
          let env = Env.add v s env in
          let t = typeof tenv env annot e in
          mk_arrow (cons s) (cons t)
        ) in
      (* NOTE: This is an optimisation (simplification of the type). *)
      let leq t1 t2 =
        let gen = TVarSet.diff (vars t1) (Env.tvars env) |> generalize in
        let t1 = Subst.apply gen t1 in
        subtype_poly t1 t2
      in
      branches |> keep_only_minimal leq |> conj_o
  in
  begin match a, annot_a with
  | Alias v, AliasA -> var_type v
  | Abstract t, AbstractA -> t
  | Const c, ConstA -> typeof_const_atom tenv c
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
  | Lambda (_, Parsing.Ast.AArrow _, _, _), LambdaA _ ->
    untypeable ("Invalid lambda: explicitely typed lambdas are not supported.")
  | Lambda (_, _, v, e), LambdaA branches -> type_lambda env branches v e
  | _, _ -> untypeable ("Invalid annotations.")
  end
  |> bot_instance |> simplify_typ
  
and typeof tenv env annot e =
  let open FullAnnot in
  begin match e, annot with
  | Var v, BVar r -> var_type v env |> rename_check [] r
  | Bind (_, v, a, e), Keep (annot_a, gen, ty, branches) ->
    let t = (* NOTE: ty different than None bypass type checking. *)
      begin match ty with
      | None -> typeof_a v tenv env annot_a a
      | Some t -> t
      end in
    let pos = Variable.get_locations v in
    let untypeable str = raise (Untypeable (pos, str)) in
    if branches = []
    then untypeable ("Invalid decomposition: cannot be empty.")
    else
      let dom = branches |> List.map fst |> disj in
      if subtype t dom
      then
        let t = generalize_check pos gen t in
        branches |> List.map (fun (s, annot) ->
          let env = Env.add v (cap t s) env in
          typeof tenv env annot e
        ) |> disj_o
      else untypeable ("Invalid decomposition: does not cover the whole domain.")
  | Bind (_, v, _, e), Skip annot ->
    assert (Env.mem v env |> not) ;
    typeof tenv env annot e
  | _, _ -> raise (Untypeable ([], "Invalid annotations."))
  end
  |> bot_instance |> simplify_typ

let typeof_a_nofail vardef tenv env annot_a a =
  try typeof_a vardef tenv env annot_a a
  with Untypeable (_, str) -> Format.printf "%a: %s@." PMsc.pp_a a str ; assert false

let typeof_nofail tenv env annot e =
  try typeof tenv env annot e
  with Untypeable (_, str) -> Format.printf "%a: %s@." PMsc.pp_e e str ; assert false  

(* ====================================== *)
(* =============== REFINE =============== *)
(* ====================================== *)

let refine_a env a t =
  log ~level:5 "refine_a@." ;
  match a with
  | Alias _ | Abstract _ | Const _ | Lambda _ -> []
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
    let dnf = Env.find v1 env |> dnf in
    let singl = List.length dnf <= 1 in
    dnf |> List.map (fun lst ->
      let ti = branch_type lst in
      let ti = bot_instance ti in
      let alpha = TVar.mk_poly None in
      let constr = [ (ti, mk_arrow (TVar.typ alpha |> cons) (cons t)) ] in
      let res = tallying constr in
      res |> List.map (fun sol ->
        let ti = apply_subst_simplify sol ti in
        let argt = Subst.find' sol alpha in
        let clean_subst =  clean_type_subst ~pos:any ~neg:empty argt in
        let ti = Subst.apply clean_subst ti in
        let argt = Subst.apply clean_subst argt in
        if singl then Env.singleton v2 argt (* Optimisation *)
        else Env.construct_dup [ (v1, ti) ; (v2, argt) ]
      )
    ) |> List.flatten
    |> List.filter
      (fun env -> env |> Env.bindings |> List.for_all (fun (_,t) -> is_mono_typ t))
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

let rec try_factorize res res_model =
  let aux (a,b) (a',b') =
    let mono = TVarSet.union (vars_mono a) (vars_mono a') in
    let mono2 = TVarSet.diff (vars_poly b) (vars_poly a) in
    match types_equiv_modulo_renaming (TVarSet.union mono mono2) a a' with
    | None -> Subst.identity
    | Some s ->
      let s' = try_factorize (Subst.apply s b) b' in
      Subst.compose s' s
  in
  if subtype res arrow_any && subtype res_model arrow_any
  then
    dnf res |> List.fold_left (fun acc arrows ->
      arrows |> List.fold_left (fun acc (a,b) ->
        dnf res_model |> List.fold_left (fun acc arrows_res ->
          arrows_res |> List.fold_left (fun acc (a',b') ->
            let s = aux (Subst.apply acc a, Subst.apply acc b) (a', b') in
            Subst.compose s acc
          ) acc
        ) acc
      ) acc
    ) Subst.identity
  else Subst.identity

let simplify_tallying res sols =
  let is_better_sol s1 s2 =
    let t1 = Subst.apply s1 res in
    let t2 = Subst.apply s2 res in
    subtype_poly t1 t2
  in
  let sols = sols |> List.map (fun sol ->
    let t = Subst.apply sol res in
    let clean = clean_type_subst ~pos:empty ~neg:any t in
    let t = Subst.apply clean t in
    let sol = Subst.compose clean sol in
    let sol =
      List.fold_left (fun sol v ->
        let t = Subst.find' sol v in
        let (a,b) = factorize (TVarSet.construct [v], TVarSet.empty) t in
        if is_empty b
        then
          (* Clean main var *)
          let clean = Subst.construct [(v, a)] in
          let sol = Subst.compose clean sol in
          let lst = Subst.rm v sol |> Subst.destruct in
          let sol = (v,a)::lst |> Subst.construct in
          sol
        else sol
      ) sol (Subst.dom sol |> TVarSet.destruct) in
    (* Decorrelate solutions *)
    let s = refresh_all (vars_poly t) in
    Subst.compose s sol
    ) in
  (* Remove weaker solutions *)
  let sols = keep_only_minimal is_better_sol sols in
  (* Rename vars to allow factorisation of arrows *)
  List.fold_left (fun sols sol ->
    let sol_res = apply_subst_simplify sol res in
    let sols_res = List.map snd sols in
    let (sol, sol_res) =
      sols_res |> List.fold_left (fun (sol, sol_res) sol_res' ->
        let s = try_factorize sol_res sol_res' in
        (Subst.compose s sol, apply_subst_simplify s sol_res)
      ) (sol, sol_res)
    in
    (sol, sol_res)::sols
  ) [] sols |> List.map fst

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
      dnf t (* |> simplify_dnf *) |> List.map (fun arrows ->
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
(* TODO: apply approximate_app for monomorphic inference too *)
(* TODO: test examples in flatten.ml, and merge them with test.ml *)
(* NOTE: Approximation for "fixpoint-like" tallying instances *)
let approximate_app t1 t2 resvar =
  let exception NoApprox in
  try
    if is_opened_arrow t2 |> not then raise NoApprox ;
    let t2s = approximate_arrow TVar.is_poly t2 in
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
(* NOTE: Approximation for tallying instances for the application *)
let approximate_app t1 t2 resvar =
  let t1s = approximate_arrow TVar.is_poly t1 in
  let res =
    t1s |> List.map (fun t1 -> approximate_app t1 t2 resvar) |> List.flatten
  in
  if res = [] && List.length t1s > 1
  then (match approximate_app t1 t2 resvar with [] -> assert false | sols -> sols)
  else res

let rec infer_inst_a vardef tenv env pannot_a a =
  let open PartialAnnot in
  let open FullAnnot in
  let vartype v = Env.find v env in
  match a, pannot_a with
  | Alias _, PartialA -> AliasA
  | Abstract _, PartialA -> AbstractA
  | Const _, PartialA -> ConstA
  | Let _, PartialA -> LetA
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
    let res = approximate_app t1 t2 alpha in
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
  | Lambda ((), _, v, e), PartialAnnot.LambdaA (b1, b2) ->
    assert (b2 = []) ;
    let branches = b1 |> List.map (fun (s, pannot) ->
      let env = Env.add v s env in
      let annot = infer_inst tenv env pannot e in
      (s, annot)
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
  | Bind ((), _, _, e), PartialAnnot.Skip pannot ->
    let annot = infer_inst tenv env pannot e in
    FullAnnot.Skip annot
  | Bind ((), v, a, e), PartialAnnot.Keep (pannot_a, branches) ->
    let annot_a = infer_inst_a v tenv env pannot_a a in
    let t = typeof_a_nofail v tenv env annot_a a in
    let gen = TVarSet.diff (vars t) (Env.tvars env) |> generalize in
    let t = Subst.apply gen t in
    let branches = branches |> List.map (fun (si, pannot) ->
      let t = cap_o t si in
      let env = Env.add v t env in
      (si, infer_inst tenv env pannot e)
    ) in
    FullAnnot.Keep (annot_a, gen, None, branches)
  | _, _ ->  assert false

(* ====================================== *)
(* =============== INFER B ============== *)
(* ====================================== *)

type 'a res =
  | Ok of 'a
  | Split of Env.t * 'a
  | Subst of (Subst.t * 'a) list
  | NeedVar of (VarSet.t * 'a * 'a option)

let map_res f res =
  match res with
  | Ok a -> Ok (f a)
  | Split (env, a) ->
    Split (env, f a)
  | Subst lst ->
    Subst (lst |> List.map (fun (s, a) -> (s, f a)))
  | NeedVar (vs, a, ao) ->
    NeedVar (vs, f a, Option.map f ao)

let needvar env vs a =
  let vs = VarSet.of_list vs in
  let vs = VarSet.diff vs (Env.domain env |> VarSet.of_list) in
  NeedVar (vs, a, None)

let is_valid_refinement env gamma =
  if VarSet.subset
    (Env.domain gamma |> VarSet.of_list)
    (Env.domain env |> VarSet.of_list)
  then
    let bindings = Env.bindings gamma in
    bindings |> List.for_all (fun (v,s) ->
      let t = Env.find v env in
      is_empty t || (cap t s |> non_empty)
    ) &&
    bindings |> List.exists (fun (v,s) ->
      let t = Env.find v env in
      cap t s |> non_empty && cap t (neg s) |> non_empty
    )
  else false

let subst_more_general s1 s2 =
  let s2m = Subst.codom s2 |> monomorphize in
  let s2 = Subst.compose s2m s2 in
  let s1g = Subst.codom s1 |> generalize in
  let s1 = Subst.compose s1g s1 in
  Subst.destruct s1 |> List.map (fun (v,t1) ->
    let t2 = Subst.find' s2 v in
    [(t1, t2) ; (t2, t1)]
  ) |> List.flatten |> tallying <> []

let simplify_tallying_infer env res sols =
  let tvars = Env.tvars env |> TVarSet.filter TVar.is_mono in
  let params_types = Env.domain env |>
    List.filter Variable.is_lambda_var |>
    List.map (fun v -> Env.find v env)
  in
  let replace_toplevel t v =
    let involved = TVarSet.diff (top_vars t) tvars in
    vars_with_polarity t |> List.filter_map (fun (v', k) ->
      if TVarSet.mem involved v' then
      match k with
      | `Pos -> Some (v', TVar.typ v)
      | `Neg -> Some (v', TVar.typ v |> neg)
      | `Both -> None
      else None
      ) |> Subst.construct
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
      let res = Subst.apply sol res in
      let res' = Subst.apply s res in
      let g = vars res' |> generalize in
      let res' = Subst.apply g res' in
      subtype_poly res' res
      (* ignore s ; false *)
    )
    in
    match res with
    | [] -> None
    | sol::_ -> Some sol
  in
  sols
  (* Generalize vars in the result when possible *)
  |> List.map (fun sol ->
    let tvars' = mono_vars sol in
    let res = Subst.apply sol res in
    let g = generalize (TVarSet.diff (vars res) tvars') in
    let res = Subst.apply g res in
    let clean = clean_type_subst ~pos:empty ~neg:any res in
    let g = Subst.compose_restr clean g in
    Subst.compose g sol
  )
  (* Remove solutions that require "undesirable" lambda branches *)
  |> List.filter (fun sol ->
    let rec is_undesirable s =
      subtype s arrow_any &&
      dnf s |> List.for_all (fun conjuncts -> conjuncts |>
        List.exists (fun (a, b) -> non_empty a && is_undesirable b)
      )
    in
    params_types |> List.for_all (fun t ->
      TVarSet.inter (vars_mono t) (Subst.dom sol) |> TVarSet.is_empty ||
      is_undesirable t || not (is_undesirable (apply_subst_simplify sol t))
    )
  )
  (* Remove solutions that require "undesirable" lambda branches *)
  (* Simplify (light) *)
  |> List.map (fun sol ->
    let new_dom = TVarSet.inter (Subst.dom sol) tvars in
    List.fold_left (fun sol v ->
      let t = Subst.find' sol v in
      let s = replace_toplevel t v in
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
    let resvars = TVarSet.diff (vars res) tvars |> TVarSet.destruct in
    let respart =
      resvars |> List.map (fun v ->
        let t =
          (* We do not simplify t, because in some cases it can be
             very complex without being used later (e.g. when no tvar to infer) *)
          to_merge |> List.map (fun s -> Subst.find' s v) |> conj
        in
        (v, t)
      ) |> Subst.construct in
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

let decorrelate_branches mono pannot_a =
  let open PartialAnnot in
  let rename_vars (t, pannot) =
    let new_vars = TVarSet.diff (vars t) mono in
    let r = refresh_all new_vars in
    (apply_subst_simplify r t, apply_subst r pannot)
  in
  match pannot_a with
  | LambdaA (branches, []) ->
    LambdaA (List.map rename_vars branches, [])
  | LambdaA _ -> assert false
  | pannot_a -> pannot_a

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
      let explored_domain = explored
        (* |> List.map (fun t ->
          let nvs = TVarSet.diff (vars t) (Env.tvars env) in
          let g = generalize nvs in let m = Subst.inverse_renaming g in
          Subst.apply g t |> clean_type ~pos:any ~neg:empty |> Subst.apply m) *)
        |> disj in
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
    aux (b1 |> List.map fst) b2 |>
      map_res (fun (b1', b2') -> LambdaA (b1@b1', b2'))
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
      log ~level:3 "@.Tallying (inference) for %a: %a <= %a@."
        Variable.pp vardef pp_typ t1 pp_typ arrow_type ;
      let res = tallying_infer [(t1, arrow_type)] in
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
        Split (Env.singleton v tau, InferA IMain)
    else
      needvar [v] (InferA IMain)
  | Ite (_, _, v1, _), InferA IThen -> needvar [v1] PartialA
  | Ite (_, _, _, v2), InferA IElse -> needvar [v2] PartialA
  | Lambda ((), Unnanoted, _, _), InferA IMain ->
    let alpha = Variable.to_typevar vardef in
    let pannot_a = LambdaA ([], [(TVar.typ alpha, Infer)]) in
    infer_branches_a vardef tenv env pannot_a a
  | Lambda ((), ADomain ts, _, _), InferA IMain ->
    let pannot_a = LambdaA ([], packannot Infer ts) in
    infer_branches_a vardef tenv env pannot_a a
  | Lambda ((), AArrow _, _, _), InferA IMain ->
    raise (Untypeable ([], "Arrows with full annotations are not supported."))
  | Lambda ((), _, v, e), LambdaA (b1, b2) ->
    if b1@b2 = [] then Subst [] else lambda v (b1,b2) e
  | _, _ -> assert false

and infer_branches tenv env pannot e =
  let needvar = needvar env in
  let open PartialAnnot in
  let split_body v t splits e =
    assert (splits <> []) ;
    let splits =
      match List.filter (fun (s, _) -> disjoint s t |> not) splits with
      | [] -> [List.hd splits]
      | splits -> splits
    in
    log ~level:2 "Typing binding for %a with splits %a.@."
      Variable.pp v (pp_list pp_typ) (List.map fst splits) ;
    let rec aux splits =
      match splits with
      | [] -> Ok []
      | (s, pannot)::splits ->
        log ~level:1 "Exploring split %a for %a.@." pp_typ s Variable.pp v ;
        let env = Env.add v (cap_o t s) env in
        begin match infer_branches_iterated tenv env pannot e with
        | Ok pannot ->
          aux splits |> map_res (fun splits -> (s, pannot)::splits)
        | Split (env', pannot) ->
          let s' = Env.find v (Env.strengthen v s env') in
          let new_splits = [ s' ; diff_o s s' ] |> List.filter non_empty in
          let new_splits = new_splits |> List.map (fun s -> (s, pannot)) in
          Split (Env.rm v env', new_splits@splits)
        | res -> res |> map_res (fun pannot -> (s, pannot)::splits)
        end
    in
    aux splits
  in
  match e, pannot with
  | Var _, Partial -> Ok Partial
  | Var v, Infer -> needvar [v] Partial
  | Bind _, Infer ->
    let pannot = Skip Infer in
    infer_branches tenv env pannot e
  | Bind ((), v, _, e), Skip pannot ->
    begin match infer_branches_iterated tenv env pannot e with
    | NeedVar (vs, pannot, Some pannot') when VarSet.mem v vs ->
      log ~level:0 "Var %a needed (optional).@." Variable.pp v ;
      let pannot = KeepSkip (InferA IMain, [(any, pannot)], pannot') in
      let pannot' = Skip pannot' in
      NeedVar (VarSet.remove v vs, pannot, Some pannot')
    | NeedVar (vs, pannot, None) when VarSet.mem v vs ->
      log ~level:0 "Var %a needed.@." Variable.pp v ;
      let pannot = Keep (InferA IMain, [(any, pannot)]) in
      NeedVar (VarSet.remove v vs, pannot, None)
    | res -> map_res (fun pannot -> Skip pannot) res
    end
  | Bind ((), v, a, _), KeepSkip (pannot_a, splits, pannot) ->
    log ~level:1 "Typing var %a (optional).@." Variable.pp v ;
    begin match infer_branches_a_iterated v tenv env pannot_a a with
    | Ok pannot_a ->
      let pannot = Keep (pannot_a, splits) in
      infer_branches tenv env pannot e
    | Subst lst when
      List.for_all (fun (s,_) -> Subst.is_identity s |> not) lst ->
      let lst = lst |> List.map (fun (s, pannot_a) ->
        (s, KeepSkip (pannot_a, splits, pannot))
      ) in
      let lst = lst@[(Subst.identity, Skip pannot)] in
      Subst lst
    | NeedVar (vs, pannot_a, None) ->
      NeedVar (vs, KeepSkip (pannot_a, splits, pannot), Some (Skip pannot))
    | res ->
      map_res (fun pannot_a -> KeepSkip (pannot_a, splits, pannot)) res
    end
  | Bind ((), v, a, e), Keep (pannot_a, splits) ->
    log ~level:1 "Typing var %a.@." Variable.pp v ;
    begin match infer_branches_a_iterated v tenv env pannot_a a with
    | Ok pannot_a ->
      let pannot_a = decorrelate_branches (Env.tvars env) pannot_a in
      let propagate = splits |> List.find_map (fun (s,_) ->
        let gammas = refine_a env a (neg s) in
        gammas |> List.find_opt (is_valid_refinement env)
      )
      in
      begin match propagate with
      | Some env' -> Split (env', Keep (pannot_a, splits))
      | None ->
        let annot_a = infer_inst_a v tenv env pannot_a a in
        let t = typeof_a_nofail v tenv env annot_a a in
        let gen = TVarSet.diff (vars t) (Env.tvars env) |> generalize in
        let t = Subst.apply gen t in
        log ~level:1 "Var %a typed with type %a.@." Variable.pp v pp_typ t ;
        split_body v t splits e |> map_res (fun splits -> Keep (pannot_a, splits))
      end
    | res -> res |> map_res (fun pannot_a -> Keep (pannot_a, splits))
    end
  | _, _ -> assert false

and infer_branches_a_iterated vardef tenv env pannot_a a =
  log ~level:5 "infer_branches_a_iterated@." ;
  match infer_branches_a vardef tenv env pannot_a a with
  | Split (gamma, pannot_a) when Env.is_empty gamma ->
    infer_branches_a_iterated vardef tenv env pannot_a a
  | Subst [(subst, pannot_a)] when Subst.is_identity subst ->
    infer_branches_a_iterated vardef tenv env pannot_a a
  | NeedVar (vs, pannot_a, _) when VarSet.is_empty vs ->
    infer_branches_a_iterated vardef tenv env pannot_a a
  | res -> res

and infer_branches_iterated tenv env pannot e =
  log ~level:5 "infer_branches_e_iterated@." ;
  match infer_branches tenv env pannot e with
  | Split (gamma, pannot) when Env.is_empty gamma ->
    infer_branches_iterated tenv env pannot e
  | Subst [(subst, pannot)] when Subst.is_identity subst ->
    infer_branches_iterated tenv env pannot e
  | NeedVar (vs, pannot, _) when VarSet.is_empty vs ->
    infer_branches_iterated tenv env pannot e
  | res -> res

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
  | Split (gamma, _) ->
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
