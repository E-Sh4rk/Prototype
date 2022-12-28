open Types.Base
open Common.Msc
open Msc
open Types.Additions
open Parsing
open Parsing.Variable
open Utils
open Common
module VarAnnot = Old_annotations.VarAnnot
(* TODO: Improve error messages
   (when failing due to all branches having failed, print errors of the branches) *)
(* TODO: Better inference of the domain of functionnal arguments
   (and then, support for recursive functions) *)

exception Ill_typed of Position.t list * string

let splits_domain splits domain =
  Format.asprintf "Splits: %a - Domain: %a"
    (Utils.pp_list pp_typ) splits pp_typ domain

let actual_expected act exp =
  Format.asprintf "Actual: %a - Expected: %a" pp_typ act pp_typ exp

let unbound_variable pos v =
  raise (Ill_typed (pos, "Unbound variable "^(Variable.show v)^"."))

let var_type pos v env =
  if Env.mem_not_absent v env then Env.find v env else unbound_variable pos v

let typeof_const_atom tenv c =
  match c with
  | Ast.Atom str -> get_atom_type tenv str
  | c -> Ast.const_to_typ c

let rec typeof_a ~legacy pos tenv env a =
  let type_lambda env va v e =
    let splits = Old_annotations.VarAnnot.splits env va in
    (* log "Lambda %a: %a@." Variable.pp v (Utils.pp_list pp_typ) splits ; *)
    if splits = []
    then raise (Ill_typed (pos, "Cannot infer domain of this abstraction."))
    else begin
      splits |> List.map (fun t ->
        let env = Env.add v t env in
        let res = typeof ~legacy tenv env e in
        mk_arrow (cons t) (cons res)
      ) |> conj_o |> simplify_typ
    end
  in
  match a with
  | Alias v -> var_type pos v env
  | Abstract t -> t
  | Const c -> typeof_const_atom tenv c
  | Pair (v1, v2) ->
    let t1 = var_type pos v1 env in
    let t2 = var_type pos v2 env in
    mk_times (cons t1) (cons t2)
  | Projection (Field label, v) -> 
    let t = var_type pos v env in
    if subtype t record_any then
      try get_field t label
      with Not_found -> raise (Ill_typed (pos, "Label " ^ label ^ " not present."))
    else
      raise (Ill_typed (pos, "Field projection can only be done on a record."))
  | Projection (p, v) ->
    let t = var_type pos v env in
    if subtype t pair_any
    then (if p = Fst then pi1 t else pi2 t)
    else raise (Ill_typed (pos, "Projection can only be done on a pair."))
  | RecordUpdate (r, label, None) -> 
    let t = var_type pos r env in
    if subtype t record_any then
      remove_field t label
    else
      raise (Ill_typed (pos, "Field removal can only be done on a record."))
  | RecordUpdate (r, label, Some v) ->
    let t = var_type pos r env in
    let t' = var_type pos v env in
    if subtype t record_any then
      let right_record = mk_record false [label, cons t'] in
      merge_records t right_record
    else
      raise (Ill_typed (pos, "Field update can only be done on a record."))
  | App (v1, v2) ->
    let t1 = var_type pos v1 env in
    if subtype t1 arrow_any
    then
      let t2 = var_type pos v2 env in
      let dom = domain t1 in
      if subtype t2 dom
      then apply t1 t2
      else raise (Ill_typed (pos,
        "Argument not in the domain of the function. "^(actual_expected t2 dom)))
    else raise (Ill_typed (pos, "Application can only be done on a function."))
  | Ite (v, t, x1, x2) ->
    let tv = var_type pos v env in
    if subtype tv empty
    then empty
    else if subtype tv t
    then var_type pos x1 env
    else if subtype tv (neg t)
    then var_type pos x2 env
    else raise (Ill_typed (pos, "Cannot select a branch for the typecase."))
  | Lambda (va, Ast.ADomain ss, v, e) ->
    let inferred_t = type_lambda env va v e in
    let dom = domain inferred_t in
    let s = disj ss in
    if equiv s dom
    then inferred_t
    else raise (Ill_typed (pos,
      "The inferred domain for the abstraction is different. "^(actual_expected dom s)))
  | Lambda (va, Ast.AArrow t, v, e) ->
    let inferred_t = type_lambda env va v e in
    if subtype inferred_t t
    then t
    else raise (Ill_typed (pos,
      "The inferred type for the abstraction is too weak. "^(actual_expected inferred_t t)))
  | Lambda (va, Unnanoted, v, e) -> type_lambda env va v e
  | Let (v1, v2) ->
    if Env.mem_not_absent v1 env
    then var_type pos v2 env
    else raise (Ill_typed (pos, "Unable to type the definition."))
  | TypeConstr _ -> failwith "Type constr unsupported."

and typeof ~legacy tenv env e =
  match e with
  | Var v -> var_type (Variable.get_locations v) v env
  | Bind (va, v, a, e) ->
    let pos = Variable.get_locations v in
    let splits = VarAnnot.splits env va in
    (* log "Bind %a: %a@." Variable.pp v (Utils.pp_list pp_typ) splits ; *)
    if splits = []
    then (
      if legacy then typeof ~legacy tenv env e
      else raise (Ill_typed (pos, "No split for this binding."))
    )
    else begin
      let d = disj_o splits in
      if has_absent d
      then (
        if legacy then assert false
        else
          let env = Env.add v absent env in
          (* NOTE: not in paper but required because inference guards annotations with \Gammas that might contain absent *)
          typeof ~legacy tenv env e
      )
      else begin
        let s = typeof_a ~legacy pos tenv env a in
        if subtype s d
        then
          splits |> List.map (fun t ->
            let env = Env.add v t env in
            typeof ~legacy tenv env e
          ) |> disj_o |> simplify_typ
        else raise (Ill_typed (pos,
          "Invalid splits (does not cover the initial domain). "^(splits_domain splits s)))
      end
    end

let refine_a = Checker.refine_a

let propagate tenv x a gammas =
  gammas |>
  List.map (fun gamma ->
    if Ref_env.mem_ref x gamma
    then refine_a ~sufficient:false tenv gamma a any (Ref_env.find x gamma)
    else [gamma]
  ) |> List.flatten

let empty_annots_a =
  map_a
  (function Bind (_, v, a, e) -> Bind (VarAnnot.empty, v, a, e) | e -> e)
  (function Lambda (_, t, v, e) -> Lambda (VarAnnot.empty, t, v, e) | a -> a)

let empty_annots_e =
  map_e
  (function Bind (_, v, a, e) -> Bind (VarAnnot.empty, v, a, e) | e -> e)
  (function Lambda (_, t, v, e) -> Lambda (VarAnnot.empty, t, v, e) | a -> a)

let restrict_annots_a gamma =
  map_a
  (function Bind (va, v, a, e) -> Bind (VarAnnot.restrict gamma va, v, a, e) | e -> e)
  (function Lambda (va, t, v, e) -> Lambda (VarAnnot.restrict gamma va, t, v, e) | a -> a)  

let restrict_annots_e gamma =
  map_e
  (function Bind (va, v, a, e) -> Bind (VarAnnot.restrict gamma va, v, a, e) | e -> e)
  (function Lambda (va, t, v, e) -> Lambda (VarAnnot.restrict gamma va, t, v, e) | a -> a)

let extract x gammas =
  let vas =
    gammas |> List.filter_map (fun envr ->
      if Ref_env.mem x envr
      then
        Some (VarAnnot.singleton
          (Ref_env.rm_deep x envr |> Ref_env.to_env)
          (Ref_env.find x envr))
      else (* None *) assert false
    ) in
  let gammas =
    gammas |> List.map (fun envr ->
      Ref_env.rm_deep x envr
    ) in
  (VarAnnot.union vas, gammas)

let typeof_a_nofail pos tenv env a =
  try typeof_a ~legacy:true pos tenv env a
  with Ill_typed _ -> assert false

(*type infer_res = e * (Env_refinement.t list) * bool (* Changes? *)*)

let rec infer_legacy' tenv env e t =
  let envr = Ref_env.from_env env |> Ref_env.push in
  match e with
  | Var v -> (e, [Ref_env.refine_old v t envr] |> filter_options, false)
  | Bind (va, v, a, e) ->
    log "@,@[<v 1>BIND for variable %a" Variable.pp v ;
    let pos = Variable.get_locations v in
    let splits = VarAnnot.splits env va in
    let res =
      if splits = []
      then begin (* BindArgSkip *)
        log "@,Skipping definition." ;
        let (e, gammas, changes) = infer_legacy' tenv env e t in
        (Bind (VarAnnot.empty, v, empty_annots_a a, e), gammas, changes)
      end else begin
        let dom_a = disj_o splits in
        let dom_a = (* NOTE: Not in the paper. Used to forward type information for explicitely typed lambdas with multiple arguments *)
          if e = Var v
          then cap_o dom_a t
          else dom_a
        in
        let (a, gammas_a, changes) = infer_legacy_a' pos tenv env a dom_a in
        if gammas_a = []
        then begin (* BindArgUntyp *)
          log "@,Skipping definition." ;
          let (e, gammas, changes) = infer_legacy' tenv env e t in
          (Bind (VarAnnot.empty, v, a (* Should be empty already *), e), gammas, changes (* true *) (* Optimisation *))
        end else if List.exists (fun envr -> Ref_env.is_empty_ref envr |> not) gammas_a
        then begin (* BindArgRefEnv *)
          log "@,The definition need refinements (going up)." ;
          let gammas =
            if List.exists Ref_env.is_empty_ref gammas_a
            then gammas_a else envr::gammas_a in
          let e = restrict_annots_e env e in
          let va = VarAnnot.restrict env va in
          (Bind (va, v, a, e), gammas, changes)
        end else if changes then begin (* BindArgRefAnns *)
          log "@,The definition need a new iteration." ;
          infer_legacy' tenv env (Bind (va, v, a, e)) t
        end else begin (* Bind *)
          log "@,The definition has been successfully annotated." ;
          let s = typeof_a_nofail pos tenv env a in
          assert (subtype s dom_a) ;
          let splits = Old_annotations.partition s splits in
          log "@,Using the following split: %a" (Utils.pp_list pp_typ) splits ;
          let res =
            splits |> List.map (fun s ->
              let (e, gammas, changes) = infer_legacy' tenv (Env.add v s env) e t in
              let changes =
                if List.length gammas >= 1 && List.for_all Ref_env.is_empty_ref gammas
                then changes (* The current annotation will not change *)
                else true (* The current annotation (or a parent) will change *)
              in
              let gammas = propagate tenv v a gammas in
              let (va, gammas) = extract v gammas in
              (va, e, gammas, changes)
            ) in
          let (vas, es, gammass, changess) = split4 res in
          let va = VarAnnot.union vas in
          let e = merge_annots_e es in
          let gammas = List.flatten gammass in
          let changes = List.exists identity changess in
          (Bind (va, v, a, e), gammas, changes)
        end
      end
    in
    log "@]@,END BIND for variable %a" Variable.pp v ; res

and infer_legacy_a' (*pos*)_ tenv env a t =
  let envr = Ref_env.from_env env |> Ref_env.push in
  let type_lambda va lt v e t ~maxdom =
    log "@,@[<v 1>LAMBDA for variable %a with t=%a" Variable.pp v pp_typ t ;
    let t = cap_o t arrow_any in
    let res =
      match dnf t |> simplify_dnf with
      | [arrows] -> (* Abs *)
        (* NOTE: Here we ignore the negative part, though we should check there is no negative part.
        But it would require a better simplification of union of arrow types to make negative parts disappear. *)
        let splits1 = VarAnnot.splits env va in
        let splits2 = List.map fst arrows in
        if splits1 = [] || (subtype (disj_o splits2) (disj_o splits1) |> not)
        then (Lambda (VarAnnot.empty, lt, v, empty_annots_e e), [], false (* Optimisation *))
        else
          let splits = splits1@splits2 in
          let splits = List.map (fun s -> cap_o s maxdom) splits in
          let splits = Old_annotations.partition_for_full_domain splits in
          log "@,Using the following split: %a" (Utils.pp_list pp_typ) splits ;
          let res =
            splits |> List.map (fun si ->
              let t = List.filter (fun (sj,_) -> subtype si sj) arrows |> List.map snd |> conj_o in
              let (e, gammas, changes) = infer_legacy' tenv (Env.add v si env) e t in
              let changes =
                if List.length gammas >= 1 && List.for_all Ref_env.is_empty_ref gammas
                then changes (* The current annotation will not change *)
                else true (* The current annotation (or a parent) will change *)
              in
              let (va, gammas) = extract v gammas in
              (va, e, gammas, changes)
            ) in
          let (vas, es, gammass, changess) = split4 res in
          let va = VarAnnot.union vas in
          let e = merge_annots_e es in
          let gammas = List.flatten gammass in
          let changes = List.exists identity changess in
          if subtype (domain t) (VarAnnot.full_domain va)
          then (Lambda (va, lt, v, e), gammas, changes)
          else (Lambda (VarAnnot.empty, lt, v, empty_annots_e e), [], false (* Optimisation *))
      | lst -> (* AbsUntypeable *)
        if lst <> [] then Format.printf "Warning: An AbsUnion rule would be needed..." ;
        (Lambda (VarAnnot.empty, lt, v, empty_annots_e e), [], false (* Optimisation *))
      in
      log "@]@,END LAMBDA for variable %a" Variable.pp v ; res
  in
  begin match a with
  | Alias v ->
    let gammas =
      [ Ref_env.refine_old v t envr ] |> filter_options in
    (a, gammas, false)
  | Abstract s when subtype s t -> (a, [envr], false)
  | Abstract _ -> (a, [], false)
  | Const c when subtype (typeof_const_atom tenv c) t -> (a, [envr], false)
  | Const _ -> (a, [], false)
  | Pair (v1, v2) ->
    if Env.mem v1 env && Env.mem v2 env then begin
      if is_empty (Env.find v1 env) || is_empty (Env.find v2 env)
      then (a, [envr], false)
      else
        let t = cap_o t pair_any in
        let gammas =
          split_pair t
          |> List.filter_map (fun (ti,si) ->
            envr |>
            option_chain [Ref_env.refine_old v1 ti ; Ref_env.refine_old v2 si]
          )
        in
        (a, gammas, false)
    end else (a, [], false)
  | Projection ((Fst|Snd), v) ->
    if Env.mem v env then begin
      let vt = Env.find v env in
      if is_empty vt then (a, [envr], false)
      else
        let t =
          match a with
          | Projection (Fst, _) -> mk_times (cons t) any_node
          | Projection (Snd, _) -> mk_times any_node (cons t)
          | _ -> assert false
        in
        let gammas =
          split_pair (cap_o vt t)
          |> List.filter_map (fun (ti,si) ->
            let t = mk_times (cons ti) (cons si) in
            Ref_env.refine_old v t envr
          )
        in
        (a, gammas, false)
    end else (a, [], false)
  | Projection (Field label, v) ->
    if Env.mem v env then begin
      let vt = Env.find v env in
      if is_empty vt then (a, [envr], false)
      else
        let t = mk_record true [label, cons t] in
        let gammas =
          split_record (cap_o vt t)
          |> List.filter_map (fun ti ->
            Ref_env.refine_old v ti envr
          )
        in
        (a, gammas, false)
    end else (a, [], false)
  | RecordUpdate (v, label, None) ->
    if Env.mem v env then begin
      let vt = Env.find v env in
      if is_empty vt then (a, [envr], false)
      else
        let t = cap_o (record_any_without label) t in
        let gammas =
          split_record t
          |> List.filter_map (fun ti ->
            let ti = remove_field_info ti label in
            Ref_env.refine_old v ti envr
          )
        in
        (a, gammas, false)
    end else (a, [], false)
  | RecordUpdate (v, label, Some f) ->
    if Env.mem v env && Env.mem f env then begin
      let vt = Env.find v env in
      let ft = Env.find f env in
      if is_empty vt || is_empty ft then (a, [envr], false)
      else
        let t = cap_o (mk_record true [label, cons ft]) t in
        let gammas =
          split_record t
          |> List.filter_map (fun ti ->
            let si = get_field ti label in
            let ti = remove_field_info ti label in
            envr |>
            option_chain [Ref_env.refine_old v ti ; Ref_env.refine_old f si]
          )
        in
        (a, gammas, false)
    end else (a, [], false)
  | Ite (v, s, v1, v2) ->
    if Env.mem v env then begin
      let vt = Env.find v env in
      if is_empty vt then (a, [envr], false)
      else
        let gammas =
          [ envr |> option_chain [Ref_env.refine_old v s       ; Ref_env.refine_old v1 t] ;
            envr |> option_chain [Ref_env.refine_old v (neg s) ; Ref_env.refine_old v2 t] ]
          |> filter_options
        in
        (a, gammas, false)
    end else (a, [], false)
  | App (v1, v2) ->
    if Env.mem v1 env && Env.mem v2 env then begin
      let vt1 = Env.find v1 env in
      let vt2 = Env.find v2 env in
      if is_empty vt1 || (is_empty vt2 && subtype vt1 arrow_any)
      then (a, [envr], false)
      else
        let vt1 = cap_o vt1 arrow_any in
        match dnf vt1 |> simplify_dnf with
        | [arrows] -> (* AppR *)
          let gammas =
            arrows |> List.filter_map (fun (si,_) ->
              let arrow_type = mk_arrow (cons (cap_o si vt2)) (cons t) in
              envr |> option_chain [
                Ref_env.refine_old v1 arrow_type ; Ref_env.refine_old v2 si
              ]
            ) in
          (a, gammas, false)
        | lst -> (* AppL *)
          let gammas =
            lst |> List.filter_map (fun arrows ->
              Ref_env.refine_old v1 (branch_type arrows) envr
            ) in
          (a, gammas, false)
    end else (a, [], false)
  | Let (v1, v2) ->
    let gammas =
      [envr |> option_chain
        [Ref_env.refine_old v1 any ; Ref_env.refine_old v2 t ]]
      |> filter_options in
      (a, gammas, false)
  | Lambda (va, (Ast.ADomain ss as lt), v, e) ->
    let s = disj ss in
    let t = cap_o t (mk_arrow (cons s) any_node) in
    type_lambda va lt v e t ~maxdom:s
  | Lambda (va, (Ast.Unnanoted as lt), v, e) ->
    let t = cap_o t arrow_any in
    type_lambda va lt v e t ~maxdom:any
  | Lambda (va, (Ast.AArrow s as lt), v, e) ->
    let t = cap_o t s in
    type_lambda va lt v e t ~maxdom:(domain s)
  | TypeConstr _ -> failwith "Type constr unsupported."
  end

let rec infer_legacy_iterated tenv e =
  match infer_legacy' tenv Env.empty e any with
  | (_, [], _) -> raise (Ill_typed ([], "Annotations inference failed."))
  | (e, _, false) -> e
  | (e, _, true) -> infer_legacy_iterated tenv e

let infer_legacy tenv env e =
  let fv = fv_e e in
  let e = VarSet.fold (fun v acc ->
    Bind (VarAnnot.initial_binding ~legacy:true, v, Abstract (var_type [] v env), acc)
  ) fv e in
  let e = infer_legacy_iterated tenv e in
  log "@." ; e

let typeof_simple_legacy tenv env e =
  let e = infer_legacy tenv env e in
  typeof ~legacy:true tenv Env.empty e |> simplify_typ

(* ========== NEW SYSTEM (LAZY) ========== *)

let typeof_a_or_absent pos tenv env a =
  try typeof_a ~legacy:false pos tenv env a
  with Ill_typed _ -> absent

let are_current_env gammas =
  gammas <> [] && List.for_all Ref_env.is_empty_ref gammas

let rec infer_a' pos tenv env a t =
  let envr = Ref_env.from_env env |> Ref_env.push in
  let type_lambda va lt v e t ~maxdom =
    log "@,@[<v 1>LAMBDA for variable %a with t=%a" Variable.pp v pp_typ t ;
    let t = cap_o t arrow_any in
    let res =
      match dnf t |> simplify_dnf with
      | [arrows] -> (* Abs *)
        (* NOTE: Here we ignore the negative part, though we should check there is no negative part.
        But it would require a better simplification of union of arrow types to make negative parts disappear. *)
        let splits = (VarAnnot.splits_or any env va)@(List.map fst arrows) in
        let splits = List.map (fun s -> cap_o s maxdom) splits in
        let splits = Old_annotations.partition_for_full_domain splits in
        log "@,Using the following split: %a" (Utils.pp_list pp_typ) splits ;
        let res =
          splits |> List.map (fun si ->
            assert (has_absent si |> not) ;
            let t = List.filter (fun (sj,_) -> subtype si sj) arrows |> List.map snd |> conj_o in
            let (e, gammas) = infer_iterated tenv (Env.add v si env) e t in
            let changes = are_current_env gammas |> not in
            let (va, gammas) = extract v gammas in
            (va, e, gammas, changes)
          ) in
        let (vas, es, gammass, changess) = split4 res in
        let va = VarAnnot.union vas in
        let e = merge_annots_e es in
        let gammas = List.flatten gammass in
        let changes = List.exists identity changess in
        if VarAnnot.is_empty va |> not && subtype (domain t) (VarAnnot.full_domain va)
        then (Lambda (va, lt, v, e), gammas, changes)
        else (* AbsUntypable *)
          (Lambda (VarAnnot.empty, lt, v, empty_annots_e e), [], false (* Optimisation *))
      | lst ->
        let (sis, gammass) =
          lst |> List.map (fun si ->
            let si = branch_type si in
            let (_, gammas) = infer_a_iterated pos tenv env a si in
            (si, gammas)
            )
            |> List.filter (fun (_,gammas) -> gammas <> [])
            |> List.split in
          let gammas = List.flatten gammass in
          if gammas = []
          then (* AbsUntypable *)
            (Lambda (VarAnnot.empty, lt, v, empty_annots_e e), [], false (* Optimisation *))
          else if are_current_env gammas
          then (* AbsUnion *)
            let t = conj_o sis in
            let (a, gammas) = infer_a_iterated pos tenv env a t in
            (a, gammas, false)
          else (* AbsUnionPropagate *)
            (a, gammas, false)
      in
      log "@]@,END LAMBDA for variable %a" Variable.pp v ; res
  in
  if has_absent t
  then begin (* Option *)
    let t = cap_o any t in
    let (a, gammas, changes) = infer_a' pos tenv env a t in
    let gammas =
      if List.exists Ref_env.is_empty_ref gammas
      then gammas else envr::gammas in
    (a, gammas, changes)
  end else begin
    begin match a with
    | Alias v ->
      let gammas =
        [ Ref_env.refine v t envr ] |> filter_options in
      (a, gammas, false)  
    | Abstract s when subtype s t -> (a, [envr], false)
    | Abstract _ -> (a, [], false)
    | Const c when subtype (typeof_const_atom tenv c) t -> (a, [envr], false)
    | Const _ -> (a, [], false)
    | Pair (v1, v2) ->
      if is_empty (Env.find v1 env)
      then (a, [Ref_env.refine v2 any envr] |> filter_options, false)
      else if is_empty (Env.find v2 env)
      then (a, [Ref_env.refine v1 any envr] |> filter_options, false)
      else begin
        let t = cap_o t pair_any in
        let gammas =
          split_pair t
          |> List.filter_map (fun (ti,si) ->
            envr |>
            option_chain [Ref_env.refine v1 ti ; Ref_env.refine v2 si]
          )
        in
        (a, gammas, false)
      end
    | Projection (typ, v) ->
      let t =
        match typ with
        | Fst -> mk_times (cons t) any_node
        | Snd -> mk_times any_node (cons t)
        | Field label -> mk_record true [label, cons t]
      in
      let gammas = [Ref_env.refine v t envr] |> filter_options in
      (a, gammas, false)
    | RecordUpdate (v, label, None) ->
      let t = cap_o (record_any_without label) t in
      let t = remove_field_info t label in
      let gammas = [Ref_env.refine v t envr] |> filter_options in
      (a, gammas, false)
    | RecordUpdate (v, label, Some f) ->
      if is_empty (Env.find v env)
      then (a, [Ref_env.refine f any envr] |> filter_options, false)
      else if is_empty (Env.find f env)
      then (a, [Ref_env.refine v record_any envr] |> filter_options, false)
      else begin
        let t = cap_o (record_any_with label) t in
        let gammas =
          split_record t
          |> List.filter_map (fun ti ->
            let si = get_field ti label in
            let ti = remove_field_info ti label in
            envr |>
            option_chain [Ref_env.refine v ti ; Ref_env.refine f si]
          )
        in
        (a, gammas, false)
      end
    | Ite (v, s, v1, v2) ->
      let vt = Env.find v env in
      let gammas =
        if is_empty vt then [envr]
        else if subtype vt s
        then [Ref_env.refine v1 t envr] |> filter_options
        else if subtype vt (neg s)
        then [Ref_env.refine v2 t envr] |> filter_options
        else [Ref_env.refine v s envr ; Ref_env.refine v (neg s) envr]
            |> filter_options
      in
      (a, gammas, false)
    | App (v1, v2) ->
      if is_empty (Env.find v1 env)
      then (a, [Ref_env.refine v2 any envr] |> filter_options, false)
      else if is_empty (Env.find v2 env)
      then (a, [Ref_env.refine v1 arrow_any envr] |> filter_options, false)
      else begin
        let vt1 = Env.find v1 env in
        let vt2 = Env.find v2 env in
        match dnf (cap_o vt1 arrow_any) |> simplify_dnf with
        | [arrows] when subtype vt2 (arrows |> List.map fst |> disj_o) -> (* AppSplitR *)
          let gammas =
            arrows |> List.filter_map (fun (si,_) ->
              let arrow_type = mk_arrow (cons (cap_o si vt2)) (cons t) in
              envr |> option_chain [
                Ref_env.refine v1 arrow_type ; Ref_env.refine v2 si
              ]
            ) in
          (a, gammas, false)
        | [arrows] when (has_absent vt1 || has_absent vt2) |> not -> (* AppWrongDom *)
          let dom = arrows |> List.map fst |> disj_o in
          let arrow_type = mk_arrow (cons vt2) (cons t) in
          let gammas =
            [Ref_env.refine v1 arrow_type envr
            (* TODO: this can actually make the final type less precise.
            See example "typeable_in_racket". *) ;
            Ref_env.refine v2 dom envr]
            |> filter_options
          in
          (a, gammas, false)
        | lst -> (* AppSplitL *)
          let gammas =
            lst |> List.filter_map (fun arrows ->
              envr |> option_chain [
                Ref_env.refine v1 (branch_type arrows) ; Ref_env.refine v2 any
              ]
            ) in
          (a, gammas, false)
      end
    | Let (v1, v2) ->
      let gammas =
        [envr |> option_chain
          [Ref_env.refine v1 any ; Ref_env.refine v2 t ]]
        |> filter_options in
        (a, gammas, false)
    | Lambda (va, (Ast.ADomain ss as lt), v, e) ->
      let s = disj ss in
      let t = cap_o t (mk_arrow (cons s) any_node) in
      type_lambda va lt v e t ~maxdom:s
    | Lambda (va, (Ast.Unnanoted as lt), v, e) ->
      let t = cap_o t arrow_any in
      type_lambda va lt v e t ~maxdom:any
    | Lambda (va, (Ast.AArrow s as lt), v, e) ->
      let t = cap_o t s in
      type_lambda va lt v e t ~maxdom:(domain s)
    | TypeConstr _ -> failwith "Type constr unsupported."
    end
  end

and infer' tenv env e t =
  let envr = Ref_env.from_env env |> Ref_env.push in
  if has_absent t
  then begin (* Option *)
    let t = cap_o any t in
    let (e, gammas, changes) = infer' tenv env e t in
    let gammas =
      if List.exists Ref_env.is_empty_ref gammas
      then gammas else envr::gammas in
    (e, gammas, changes)
  end else begin
    match e with
    | Var v -> (e, [Ref_env.refine v t envr] |> filter_options, false)
    | Bind (va, v, a, e) ->
      log "@,@[<v 1>BIND for variable %a" Variable.pp v ;
      let pos = Variable.get_locations v in
      let splits = VarAnnot.splits_or any_or_absent env va in
      let res =
        if List.for_all has_absent splits
        then (* BindArgSkip *)
          let s = disj_o splits in
          log "@,Skipping definition." ;
          let env = Env.add v s env in
          let (e, gammas) = infer_iterated tenv env e t in
          let changes = are_current_env gammas |> not in
          let (va, gammas) = extract v gammas in
          (Bind (va, v, restrict_annots_a env a, e), gammas, changes)
        else begin
          let dom_a = disj_o splits in
          let (a, gammas_a) = infer_a_iterated pos tenv env a dom_a in
          if gammas_a = []
          then begin (* BindArgUntyp *)
            log "@,Untypable definition..." ;
            (Bind (VarAnnot.empty, v, a (* Should be empty already *), empty_annots_e e),
            [], true)
          end else if are_current_env gammas_a |> not
          then begin (* BindArgRefEnv *)
              log "@,The definition need refinements (going up)." ;
              let e = restrict_annots_e env e in
              let va = VarAnnot.restrict env va in
              (Bind (va, v, a, e), gammas_a, true)
          end else begin
            log "@,The definition has been successfully annotated." ;
            let s = typeof_a_or_absent pos tenv env a in
            (*Format.printf "%s@." (actual_expected s dom_a) ;*)
            assert (subtype s dom_a) ;
            let splits = Old_annotations.partition s splits in
            log "@,Using the following split: %a" (Utils.pp_list pp_typ) splits ;
            let to_propagate =
              if List.length splits > 1
              then
                splits |>
                List.map (fun si -> refine_a ~sufficient:false tenv envr a s si) |>
                List.concat
              else [envr]
            in
            if are_current_env to_propagate |> not
            then begin (* BindPropagateSplit *)
              log "@,... but first some constraints must be propagated." ;
              let va =
                List.map (fun si -> VarAnnot.singleton env si) splits |>
                VarAnnot.union in
              let e = restrict_annots_e env e in
              (Bind (va, v, a, e), to_propagate, true)
            end else begin (* Bind *)
              let res =
                splits |> List.map (fun si ->
                  let (e, gammas) = infer_iterated tenv (Env.add v si env) e t in
                  let changes = are_current_env gammas |> not in
                  let (va, gammas) = extract v gammas in
                  (va, e, gammas, changes)
              ) in
              let (vas, es, gammass, changess) = split4 res in
              let va = VarAnnot.union vas in
              let e = merge_annots_e es in
              let gammas = List.flatten gammass in
              let changes = List.exists identity changess in
              (Bind (va, v, a, e), gammas, changes)
            end
          end
        end
      in
      log "@]@,END BIND for variable %a" Variable.pp v ; res
  end

and infer_a_iterated pos tenv env a t =
    match infer_a' pos tenv env a t with
    | (a, gammas, true) when are_current_env gammas ->
      infer_a_iterated pos tenv env a t
    | (a, gammas, _) -> (a, gammas)

and infer_iterated tenv env e t =
  match infer' tenv env e t with
  | (e, gammas, true) when are_current_env gammas ->
    infer_iterated tenv env e t
  | (e, gammas, _) -> (e, gammas)

let infer tenv env e =
  let fv = fv_e e in
  let e = VarSet.fold (fun v acc ->
    Bind (VarAnnot.initial_binding ~legacy:false, v, Abstract (var_type [] v env), acc)
  ) fv e in
  let e =
    match infer_iterated tenv Env.empty e any with
    | (_, []) -> raise (Ill_typed ([], "Annotations inference failed."))
    | (e, _) -> e
  in
  log "@." ; e

let typeof_simple tenv env e =
  let e = infer tenv env e in
  typeof ~legacy:false tenv Env.empty e |> simplify_typ
