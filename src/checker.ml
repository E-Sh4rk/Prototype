open Cduce
open Nf_ast
open Types_additions
open Annotations
open Variable
open Utils
(* TODO: Improve error messages
   (when failing due to all branches having failed, print errors of the branches) *)
(* TODO: Better inference of the domain of functionnal arguments
   (and then, support for recursive functions) *)
(* TODO: Cduce type printer should add some parentheses sometimes
   (ambiguous for arrows and regex) *)

exception Ill_typed of Position.t list * string

let splits_domain splits domain =
  Format.asprintf "Splits: %a - Domain: %a"
    (Utils.pp_list Cduce.pp_typ) splits Cduce.pp_typ domain

let actual_expected act exp =
  Format.asprintf "Actual: %a - Expected: %a" pp_typ act pp_typ exp

let unbound_variable pos v =
  raise (Ill_typed (pos, "Unbound variable "^(Variable.show v)^"."))

let var_type pos v env =
  if Env.mem v env then Env.find v env else unbound_variable pos v

let typeof_const_atom tenv c =
  match c with
  | Ast.Atom str -> get_type tenv str
  | c -> Ast.const_to_typ c

let rec typeof_a pos tenv env a =
  let type_lambda env va v e =
    let splits = VarAnnot.splits env va in
    if splits = []
    then raise (Ill_typed (pos, "Cannot infer domain of this abstraction."))
    else begin
      splits |> List.map (fun t ->
        let env = Env.add v t env in
        let res = typeof tenv env e in
        mk_arrow (cons t) (cons res)
      ) |> conj |> simplify_typ
    end
  in
  match a with
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
  | Lambda (va, Ast.ADomain s, v, e) ->
    let inferred_t = type_lambda env va v e in
    let dom = domain inferred_t in
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
    if Env.mem v1 env
    then var_type pos v2 env
    else raise (Ill_typed (pos, "Unable to type the definition."))

and typeof tenv env e =
  match e with
  | Var v -> var_type (Variable.get_locations v) v env
  | Bind (va, v, a, e) ->
    let splits = VarAnnot.splits env va in
    if splits = []
    then typeof tenv env e
    else begin
      let pos = Variable.get_locations v in
      let s = typeof_a pos tenv env a in
      if disj splits |> equiv s
      (* NOTE: it is still sound if we only test 'subtype' instad of 'equiv',
        but for now I prefer to match the paper. *)
      then
        splits |> List.map (fun t ->
          let env = Env.add v t env in
          typeof tenv env e
        ) |> disj |> simplify_typ
      else raise (Ill_typed (pos,
        "Invalid splits (does not cover the initial domain). "^(splits_domain splits s)))
    end

let refine_a tenv env a t =
  match a with
  | Abstract s -> if disjoint s t then [] else [env]
  | Const c -> if disjoint (typeof_const_atom tenv c) t then [] else [env]
  | Pair (v1, v2) ->
    split_pair t
    |> List.filter_map (
      fun (t1, t2) ->
        env |>
        option_chain [Env_refinement.refine v1 t1 ; Env_refinement.refine v2 t2]
    )
  | Projection (Fst, v) -> [Env_refinement.refine v (mk_times (cons t) any_node) env] |> filter_options
  | Projection (Snd, v) -> [Env_refinement.refine v (mk_times any_node (cons t)) env] |> filter_options
  | Projection (Field label, v) ->
    [Env_refinement.refine v (mk_record true [label, cons t]) env] |> filter_options
  | RecordUpdate (v, label, None) ->
    let t = cap_o t (record_any_without label) in
    split_record t
    |> List.filter_map (
      fun ti ->
          let ti = remove_field_info ti label in
          Env_refinement.refine v ti env
    )
  | RecordUpdate (v, label, Some x) ->
    split_record t
    |> List.filter_map (
      fun ti ->
        let field_type = get_field_assuming_not_absent ti label in
        let ti = remove_field_info ti label in
        env |>
        option_chain [Env_refinement.refine v ti ; Env_refinement.refine x field_type]
      )
  | App (v1, v2) ->
    let t1 = Env_refinement.find v1 env in
    square_split t1 t
    |> List.filter_map (
      fun (t1, t2) ->
        env |>
        option_chain [Env_refinement.refine v1 t1 ; Env_refinement.refine v2 t2]
    )
  | Ite (v, s, x1, x2) ->
    [ env |> option_chain [Env_refinement.refine v s       ; Env_refinement.refine x1 t] ;
      env |> option_chain [Env_refinement.refine v (neg s) ; Env_refinement.refine x2 t] ]
    |> filter_options
  | Lambda _ ->
    if disjoint arrow_any t then [] else [env]
  | Let (v1, v2) ->
    [ env |>
    option_chain [Env_refinement.refine v1 any ; Env_refinement.refine v2 t]]
    |> filter_options

let propagate tenv x a gammas =
  gammas |>
  List.map (fun gamma ->
    if Env_refinement.has_refinement x gamma
    then refine_a tenv gamma a (Env_refinement.find x gamma)
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

let restrict_annots gamma =
  map_e
  (function Bind (va, v, a, e) -> Bind (VarAnnot.restrict gamma va, v, a, e) | e -> e)
  (function Lambda (va, t, v, e) -> Lambda (VarAnnot.restrict gamma va, t, v, e) | a -> a)

(*let merge_annots_a default a_s =
  try merge_annots_a a_s with Not_found -> empty_annots_a default*)
let merge_annots_e default es =
  try merge_annots_e es with Not_found -> empty_annots_e default

let extract x gammas =
  let vas =
    gammas |> List.map (fun envr ->
      VarAnnot.singleton
        (Env_refinement.rm x envr |> Env_refinement.to_env)
        (Env_refinement.find x envr)
    ) in
  let gammas =
    gammas |> List.map (fun envr ->
      Env_refinement.rm x envr
    ) in
  (VarAnnot.union vas, gammas)

(*let typeof_nofail tenv env e =
  try typeof tenv env e
  with Ill_typed _ -> assert false*)

let typeof_a_nofail pos tenv env a =
  try typeof_a pos tenv env a
  with Ill_typed _ -> assert false

(*type infer_res = e * (Env_refinement.t list) * bool (* Finished? *)*)

(* TODO: Instead of this "finished" flag, use a "annotations modified" flag
(more similar to the paper, and I think there might be some problems with the current system where one last teration is missing) *)

let normalize_output_a (a,gammas,finished) =
  if gammas = []
  then (empty_annots_a a(* Just to be sure *),gammas,true)
  else (a,gammas,finished)

let normalize_output_e (e,gammas,finished) =
  if gammas = []
  then (empty_annots_e e(* Just to be sure *),gammas,true)
  else (e,gammas,finished)

let rec infer' tenv env e t =
  let envr = Env_refinement.empty env in
  match e with
  | Var v -> (e, [Env_refinement.refine v t envr] |> filter_options, true)
  | Bind (va, v, a, e) ->
    log "@,@[<v 1>BIND for variable %a" Variable.pp v ;
    let pos = Variable.get_locations v in
    let splits = VarAnnot.splits env va in
    let dom_a = disj splits in
    let res =
      if splits = []
      then begin (* BindArgSkip *)
        log "@,Skipping definition." ;
        let (e, gammas, finished) = infer' tenv env e t in
        (Bind (VarAnnot.empty, v, empty_annots_a a, e), gammas, finished)
      end else begin
        let (a, gammas_a, finished) = infer_a' pos tenv env a dom_a in
        if gammas_a = []
        then begin (* BindArgUntyp *)
          log "@,Skipping definition." ;
          let (e, gammas, finished) = infer' tenv env e t in
          (Bind (VarAnnot.empty, v, a (* should be empty already *), e), gammas, finished)
        end else if List.exists (fun envr -> Env_refinement.is_empty envr |> not) gammas_a
        then begin (* BindArgRefEnv *)
          log "@,The definition need refinements (going up)." ;
          let gammas =
            if List.exists Env_refinement.is_empty gammas_a
            then gammas_a else envr::gammas_a in
          let e = restrict_annots env e in
          let va = VarAnnot.restrict env va in
          (Bind (va, v, a, e), gammas, false)
        end else if not finished then begin (* BindArgRefAnns *)
          log "@,The definition need a new iteration." ;
          infer' tenv env (Bind (va, v, a, e)) t
        end else begin (* Bind *)
          log "@,The definition has been successfully annotated." ;
          let s = typeof_a_nofail pos tenv env a in
          (* if subtype s dom_a |> not
          then Format.printf "%a@.%s@." pp_a a (actual_expected s dom_a) ;*)
          assert (subtype s dom_a) ;
          let splits = partition s splits in
          log "@,Using the following split: %a" (Utils.pp_list Cduce.pp_typ) splits ;
          let res =
            splits |> List.map (fun s ->
              let (e, gammas, finished) = infer' tenv (Env.add v s env) e t in
              let gammas = propagate tenv v a gammas in
              let (va, gammas) = extract v gammas in
              (* If the splits for this definition have changed, we must retype the definition. *)
              let finished =
                if subtype s (VarAnnot.splits env va |> disj)
                then finished
                else false
              in
              (va, e, gammas, finished)
            ) in
          let (vas, es, gammass, finisheds) = split4 res in
          let va = VarAnnot.union vas in
          let e = merge_annots_e e es in
          let gammas = List.flatten gammass in
          let finished = List.for_all identity finisheds in
          (Bind (va, v, a, e), gammas, finished)
        end
      end
    in
    log "@]@,END BIND for variable %a" Variable.pp v ; normalize_output_e res

and infer_a' (*pos*)_ tenv env a t =
  let envr = Env_refinement.empty env in
  let type_lambda va lt v e t ~maxdom =
    log "@,@[<v 1>LAMBDA for variable %a with t=%a" Variable.pp v pp_typ t ;
    let t = cap_o t arrow_any in
    (* NOTE: In the paper, the rule AbsUnion does not interstect t with arrow_any *)
    let res =
      match dnf t |> simplify_dnf with
      | [arrows] -> (* Abs *)
        (* NOTE: Here we ignore the negative part, though we should check there is no negative part.
        But it would require a better simplification of union of arrow types to make negative parts disappear. *)
        let splits1 = VarAnnot.splits env va in
        let splits2 = List.map fst arrows in
        if splits1 = [] || (subtype (disj splits2) (disj splits1) |> not)
        then (Lambda (VarAnnot.empty, lt, v, empty_annots_e e), [], true)
        else
          let splits = splits1@splits2 in
          let splits = List.map (fun s -> cap_o s maxdom) splits in
          let splits = partition_for_full_domain splits in
          log "@,Using the following split: %a" (Utils.pp_list Cduce.pp_typ) splits ;
          let res =
            splits |> List.map (fun si ->
              let (e, gammas, finished) = infer' tenv (Env.add v si env) e (apply_opt t si) in
              let (va, gammas) = extract v gammas in
              (va, e, gammas, finished)
            ) in
          let (vas, es, gammass, finisheds) = split4 res in
          let va = VarAnnot.union vas in
          let e = merge_annots_e e es in
          let gammas = List.flatten gammass in
          let finished = List.for_all identity finisheds in
          if subtype (domain t) (VarAnnot.full_domain va)
          then (Lambda (va, lt, v, e), gammas, finished)
          else (Lambda (VarAnnot.empty, lt, v, empty_annots_e e), [], true)
      | lst -> (* AbsUntypeable *)
        if lst <> [] then Format.printf "Warning: An AbsUnion rule would be needed..." ;
        (Lambda (VarAnnot.empty, lt, v, empty_annots_e e), [], true)
      in
      log "@]@,END LAMBDA for variable %a" Variable.pp v ; res
  in
  begin match a with
  | Abstract s when subtype s t -> (a, [envr], true)
  | Abstract _ -> (a, [], true)
  | Const c when subtype (typeof_const_atom tenv c) t -> (a, [envr], true)
  | Const _ -> (a, [], true)
  | Pair (v1, v2) ->
    if Env.mem v1 env && Env.mem v2 env then begin
      if is_empty (Env.find v1 env) || is_empty (Env.find v2 env)
      then (a, [envr], true)
      else
        let t = cap_o t pair_any in
        let gammas =
          split_pair t
          |> List.filter_map (fun (ti,si) ->
            envr |>
            option_chain [Env_refinement.refine v1 ti ; Env_refinement.refine v2 si]
          )
        in
        (a, gammas, true)
    end else (a, [], true)
  | Projection ((Fst|Snd), v) ->
    if Env.mem v env then begin
      let vt = Env.find v env in
      if is_empty vt then (a, [envr], true)
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
            Env_refinement.refine v t envr
          )
        in
        (a, gammas, true)
    end else (a, [], true)
  | Projection (Field label, v) ->
    if Env.mem v env then begin
      let vt = Env.find v env in
      if is_empty vt then (a, [envr], true)
      else
        let t = mk_record true [label, cons t] in
        let gammas =
          split_record (cap_o vt t)
          |> List.filter_map (fun ti ->
            Env_refinement.refine v ti envr
          )
        in
        (a, gammas, true)
    end else (a, [], true)
  | RecordUpdate (v, label, None) ->
    if Env.mem v env then begin
      let vt = Env.find v env in
      if is_empty vt then (a, [envr], true)
      else
        let t = cap_o (record_any_without label) t in
        let gammas =
          split_record t
          |> List.filter_map (fun ti ->
            let ti = remove_field_info ti label in
            Env_refinement.refine v ti envr
          )
        in
        (a, gammas, true)
    end else (a, [], true)
  | RecordUpdate (v, label, Some f) ->
    if Env.mem v env && Env.mem f env then begin
      let vt = Env.find v env in
      let ft = Env.find f env in
      if is_empty vt || is_empty ft then (a, [envr], true)
      else
        let t = cap_o (mk_record true [label, cons ft]) t in
        let gammas =
          split_record t
          |> List.filter_map (fun ti ->
            let si = get_field ti label in
            let ti = remove_field_info ti label in
            envr |>
            option_chain [Env_refinement.refine v ti ; Env_refinement.refine f si ]
          )
        in
        (a, gammas, true)
    end else (a, [], true)
  | Ite (v, s, v1, v2) ->
    if Env.mem v env then begin
      let vt = Env.find v env in
      if is_empty vt then (a, [envr], true)
      else
        let gammas =
          [ envr |> option_chain [Env_refinement.refine v s       ; Env_refinement.refine v1 t] ;
            envr |> option_chain [Env_refinement.refine v (neg s) ; Env_refinement.refine v2 t] ]
          |> filter_options
        in
        (a, gammas, true)
    end else (a, [], true)
  | App (v1, v2) ->
    if Env.mem v1 env && Env.mem v2 env then begin
      let vt1 = Env.find v1 env in
      let vt2 = Env.find v2 env in
      if is_empty vt1 || (is_empty vt2 && subtype vt1 arrow_any)
      then (a, [envr], true)
      else
        let vt1 = cap_o vt1 arrow_any in
        (* NOTE: In the paper, the rule AppR does not interstect vt1 with arrow_any *)
        match dnf vt1 |> simplify_dnf with
        | [arrows] -> (* AppR *)
          let gammas =
            arrows |> List.filter_map (fun (si,_) ->
              let arrow_type = mk_arrow (cons (cap_o si vt2)) (cons t) in
              let arg = (cap_o si vt2) in
              if (is_empty arg |> not) && (subtype vt1 arrow_type) && (subtype (apply vt1 arg) (apply arrow_type arg) |> not)
              then begin
                Format.printf "t:%a@.arrow_needed:%a@.simplified vt1:%a@.vt2:%a@.si:%a@." pp_typ t pp_typ arrow_type pp_typ (simplify_typ vt1) pp_typ vt2 pp_typ si ;
                failwith "Cduce error :("
              end ;
              envr |> option_chain [
                Env_refinement.refine v1 arrow_type ; Env_refinement.refine v2 si
              ]
            ) in
          (a, gammas, true)
        | lst -> (* AppL *)
          let gammas =
            lst |> List.filter_map (fun arrows ->
              Env_refinement.refine v1 (branch_type arrows) envr
            ) in
          (a, gammas, false)
    end else (a, [], true)
  | Let (v1, v2) ->
    let gammas =
      [envr |> option_chain
        [Env_refinement.refine v1 any ; Env_refinement.refine v2 t ]]
      |> filter_options in
      (a, gammas, true)
  | Lambda (va, (Ast.ADomain s as lt), v, e) ->
    let t = cap_o t (mk_arrow (cons s) any_node) in
    type_lambda va lt v e t ~maxdom:s
  | Lambda (va, (Ast.Unnanoted as lt), v, e) ->
    let t = cap_o t arrow_any in
    type_lambda va lt v e t ~maxdom:any
  | Lambda (va, (Ast.AArrow s as lt), v, e) ->
    let t = cap_o t s in
    type_lambda va lt v e t ~maxdom:(domain s)
  end
  |> normalize_output_a

let rec infer_iterated tenv e =
  match infer' tenv Env.empty e any with
  | (_, [], _) -> raise (Ill_typed ([], "Annotations inference failed."))
  | (e, _, true) -> e
  | (e, _, false) -> infer_iterated tenv e

let infer tenv env e =
  let fv = fv_e e in
  let e = VarSet.fold (fun v acc ->
    Bind (VarAnnot.initial, v, Abstract (var_type [] v env), acc)
  ) fv e in
  let e = infer_iterated tenv e in
  log "@." ; e

let typeof_simple tenv env e =
  let e = infer tenv env e in
  typeof tenv Env.empty e |> simplify_typ
