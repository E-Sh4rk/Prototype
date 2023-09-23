open Types.Base
open Types.Tvar
open Types.Additions
open Parsing.Variable

module Domains = struct
  type t = Env.t list
  [@@deriving show]
  let add lst e =
    let e = Env.filter (fun x _ -> Variable.is_lambda_var x) e in
    let tvars = Env.tvars e |> TVarSet.filter TVar.can_infer in
    let e = Env.apply_subst (generalize tvars) e in
    e::lst
  let more_specific dom env1 env2 =
    dom |> List.map (fun v ->
      (Env.find v env1, Env.find v env2)
    ) |> subtypes_poly
  let covers t1 t2 =
    t2 |> List.for_all (fun env2 ->
      let dom2 = Env.domain env2 |> VarSet.of_list in
      let has_same_vars env =
        let dom = Env.domain env |> VarSet.of_list in
        VarSet.equal dom dom2
      in
      let dom2 = VarSet.elements dom2 in
      let type_for env =
        dom2 |> List.fold_left (fun acc v ->
          let t = Env.find v env in
          mk_times (cons acc) (cons t)
        ) any
      in
      let more_specific = more_specific dom2 in
      let a = t1 |> List.filter has_same_vars
      |> List.filter (fun env1 -> more_specific env1 env2)
      |> List.map type_for in
      let s = reduce_tvars a in (* NOTE: approximation *)
      let a = a |> List.map (Subst.apply s) |> disj_o in
      let b = type_for env2 in
      supertype_poly a b
    )
  let enter_lambda env' t =
    let env' = env' |> Env.filter (fun v _ -> Variable.is_lambda_var v) in
    let dom' = Env.domain env' |> VarSet.of_list in
    let more_specific = more_specific (VarSet.elements dom') in
    t |> List.filter (fun env ->
      let dom = Env.domain env |> VarSet.of_list in
      if VarSet.diff dom' dom |> VarSet.is_empty
      then more_specific env env'
      else false
    )
  let empty = []
  let cup = (@)
  let singleton e = add empty e
end

module FullAnnot = struct
  type 'a inter = 'a list
  [@@deriving show]
  type inst = Subst.t list
  [@@deriving show]
  type renaming = Subst.t
  [@@deriving show]
  type union = (typ * t) list
  [@@deriving show]
  and a =
      | ConstA | AliasA | LetA | AbstractA
      | LambdaA of typ * t
      | PairA of renaming * renaming
      | AppA of inst * inst
      | ProjA of inst
      | EmptyA of inst | ThenA of inst | ElseA of inst
      | RecordUpdateA of inst * (renaming option)
      | ConstrA of inst
      | InterA of a inter
  [@@deriving show]
  and t =
      | BVar of renaming
      | Keep of a * union * inst
      | Skip of t
      | Inter of t inter
  [@@deriving show]
end

module PartialAnnot = struct
  type 'a cache = { depends_on:VarSet.t ; annot_changed:bool ;
    prev_typ:typ option ; prev_fa:'a option }
  let pp_cache _ fmt _ = Format.fprintf fmt "cache"
  type union_expl = (typ * t_cached) list
  [@@deriving show]
  and union_done = (typ * t_cached) list
  [@@deriving show]
  and union_unr = typ list
  [@@deriving show]
  and union = union_expl * union_done * union_unr
  [@@deriving show]
  and 'a pending_branch =
      'a
      * Domains.t (* Domains involved (used to prune branches) *)
      * bool (* Low priority default: type only if no other branch is typeable *)
  [@@deriving show]
  and 'a inter = ('a pending_branch) list (* Pending *)
               * 'a list (* Explored *)
               * (Domains.t (* Explored domains *)
                  * bool (* Typing finished? *)
                  * bool (* User defined *))
  [@@deriving show]
  and a =
      | InferA | TypA | UntypA
      | ThenVarA | ElseVarA
      | EmptyA | ThenA | ElseA (* NOTE: not in the paper, small optimisation *)
      | LambdaA of typ * t_cached
      | InterA of a_cached inter
  [@@deriving show]
  and t =
      | Infer | Typ | Untyp
      | Keep of a_cached * union
      | Skip of t_cached
      | TrySkip of t_cached
      | TryKeep of a_cached * t_cached * t_cached
      | Propagate of a_cached * (Env.t * union) list * union
      | Inter of t_cached inter
  [@@deriving show]
  and a_cached = a * FullAnnot.a cache
  [@@deriving show]
  and t_cached = t * FullAnnot.t cache
  [@@deriving show]

  let update_cache changed c =
    if changed
    then { c with annot_changed = true }
    else c

  let rec apply_subst_aux s =
    if Subst.is_identity s then ((fun t -> (t,false)), (fun a -> (a,false)))
    else
      let dom = Subst.dom s in
      let change = ref false in
      let update_change b = change := b || !change in
      let apply_typ t =
        if TVarSet.inter (vars t) dom |> TVarSet.is_empty
        then t else (change := true ; apply_subst_simplify s t)
      and apply_subst_a a =
        let (a, changed) = apply_subst_a s a in
        update_change changed ; a
      and apply_subst t =
        let (t, changed) = apply_subst s t in
        update_change changed ; t
      in
      let apply_a a = match a with
        | InferA -> InferA
        | TypA -> TypA
        | UntypA -> UntypA
        | ThenVarA -> ThenVarA | ElseVarA -> ElseVarA
        | EmptyA -> EmptyA | ThenA -> ThenA | ElseA -> ElseA
        | LambdaA (ty, t) -> LambdaA (apply_typ ty, apply_subst t)
        | InterA (a, b, flags) -> InterA (
          List.map (fun (a,d,b) -> (apply_subst_a a,d,b)) a,
          List.map apply_subst_a b,
          flags)
      and apply t =
        let apply_subst_union (e,d,u) =
          let aux2 (ty, t) = (apply_typ ty, apply_subst t) in
          (List.map aux2 e, List.map aux2 d, List.map apply_typ u)
        in
        match t with
        | Infer -> Infer
        | Typ -> Typ
        | Untyp -> Untyp
        | Keep (a, b) -> Keep (apply_subst_a a, apply_subst_union b)
        | Skip t -> Skip (apply_subst t)
        | TrySkip t -> TrySkip (apply_subst t)
        | TryKeep (a, t1, t2) ->
          TryKeep (apply_subst_a a, apply_subst t1, apply_subst t2)
        | Propagate (a, envs, t) ->
          let aux2 (env, t) =
            (Env.apply_subst s env, apply_subst_union t)
          in
          Propagate (apply_subst_a a, List.map aux2 envs, apply_subst_union t)
        | Inter (a, b, flags) -> Inter (
          List.map (fun (a,d,b) -> (apply_subst a,d,b)) a,
          List.map apply_subst b,
          flags)
      in
      ((fun t -> let res = apply t in (res, !change)),
        (fun a -> let res = apply_a a in (res, !change)))    

  and apply_subst_a s (a,c) =
    let (_, apply_subst_a) = apply_subst_aux s in
    let (a,b) = apply_subst_a a in
    let c = update_cache b c in
    ((a,c),b)

  and apply_subst s (t,c) =
    let (apply_subst, _) = apply_subst_aux s in
    let (t,b) = apply_subst t in
    let c = update_cache b c in
    ((t,c),b)

  let apply_subst_a s a = apply_subst_a s a |> fst
  let apply_subst s t = apply_subst s t |> fst

  let init_cache_a a =
    { depends_on = Msc.fv_a a ; annot_changed = false ;
      prev_typ = None ; prev_fa = None }
  let init_cache t =
    { depends_on = Msc.fv_e t ; annot_changed = false ;
      prev_typ = None ; prev_fa = None }
  let init_cache' vs =
    { depends_on = vs ; annot_changed = false ;
      prev_typ = None ; prev_fa = None }
end
