open Types.Base
open Types.Tvar
open Types.Additions
open Parsing.Variable

module Domains = struct
  type t = Env.t list
  [@@deriving show]
  let add lst mono e =
    let e = Env.filter (fun x _ -> Variable.is_lambda_var x) e in
    let tvars = Env.tvars e |> TVarSet.filter TVar.can_infer in
    let tvars = TVarSet.diff tvars mono in
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
      |> List.map type_for |> disj_o in
      let b = type_for env2 in
      supertype_poly a b
    )
  let empty = []
  let enter_lambda _ _ _ = empty
  let cup = (@)
  let singleton mono e = add empty mono e
  let apply_subst s = List.map (Env.apply_subst s)
end

module FullAnnot = struct
  type cache = { mutable typ: typ option }
  let pp_cache fmt _ = Format.fprintf fmt "cache"
  type 'a inter = 'a list
  [@@deriving show]
  type inst = Subst.t list
  [@@deriving show]
  type renaming = Subst.t
  [@@deriving show]
  type union = (typ * t_cached) list
  [@@deriving show]
  and a =
      | ConstA | AliasA | LetA | AbstractA
      | LambdaA of typ * t_cached
      | PairA of renaming * renaming
      | AppA of inst * inst
      | ProjA of inst
      | EmptyA of inst | ThenA of inst | ElseA of inst
      | RecordUpdateA of inst * (renaming option)
      | ConstrA of inst
      | InterA of a_cached inter
  [@@deriving show]
  and t =
      | BVar of renaming
      | Keep of a_cached * union * inst
      | Skip of t_cached
      | Inter of t_cached inter
  [@@deriving show]
  and a_cached = a * cache
  [@@deriving show]
  and t_cached = t * cache
  [@@deriving show]

  let init_cache () = { typ = None }

  let rec clear_cache (t, _) =
    let t = match t with
    | Keep (a, u, i) ->
      let aux (typ, t) = (typ, clear_cache t) in
      Keep (clear_cache_a a, List.map aux u, i)
    | Skip t -> Skip (clear_cache t)
    | BVar r -> BVar r
    | Inter lst -> Inter (List.map clear_cache lst)
    in
    (t, init_cache ())

  and clear_cache_a (a, _) =
  let a = match a with
  | ConstA | AliasA | LetA | AbstractA |PairA _ | AppA _ | ProjA _
  | EmptyA _ | ThenA _ | ElseA _ | RecordUpdateA _ | ConstrA _ -> a
  | InterA lst -> InterA (List.map clear_cache_a lst)
  | LambdaA (typ, t) -> LambdaA (typ, clear_cache t)
  in
  (a, init_cache ())
end

module PartialAnnot = struct
  type union_expl = (typ * t) list
  [@@deriving show]
  and union_done = (typ * t) list
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
      | LambdaA of typ * t
      | InterA of a inter
  [@@deriving show]
  and t =
      | Infer | Typ | Untyp
      | Keep of a * union
      | Skip of t
      | TrySkip of t
      | TryKeep of a * t * t
      | Propagate of a * (Env.t * int) list * union
      | Inter of t inter
  [@@deriving show]

  (* === APPLY_SUBST === *)

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
      let apply_inter apply_branch (a, b, (d,tf,ud)) =
        (
          List.map (fun (a,d,b) -> (apply_branch a,Domains.apply_subst s d,b)) a,
          List.map apply_branch b,
          (Domains.apply_subst s d,tf,ud)
        )
      in
      let apply_a a = match a with
        | InferA -> InferA
        | TypA -> TypA
        | UntypA -> UntypA
        | ThenVarA -> ThenVarA | ElseVarA -> ElseVarA
        | EmptyA -> EmptyA | ThenA -> ThenA | ElseA -> ElseA
        | LambdaA (ty, t) -> LambdaA (apply_typ ty, apply_subst t)
        | InterA i -> InterA (apply_inter apply_subst_a i)
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
          let aux2 (env, i) = (Env.apply_subst s env, i) in
          Propagate (apply_subst_a a, List.map aux2 envs, apply_subst_union t)
        | Inter i -> Inter (apply_inter apply_subst i)
      in
      ((fun t -> let res = apply t in (res, !change)),
        (fun a -> let res = apply_a a in (res, !change)))    

  and apply_subst_a s a =
    let (_, apply_subst_a) = apply_subst_aux s in
    let (a,b) = apply_subst_a a in
    (* let c = update_cache b c in *)
    (a,b)

  and apply_subst s t =
    let (apply_subst, _) = apply_subst_aux s in
    let (t,b) = apply_subst t in
    (* let c = update_cache b c in *)
    (t,b)

  let apply_subst_a s a = apply_subst_a s a |> fst
  let apply_subst s t = apply_subst s t |> fst

  (* === EQUALS (for caching) === *)

  let rec equals_a a1 a2 =
    match a1, a2 with
    | InferA, InferA | TypA, TypA | UntypA, UntypA
    | ThenVarA, ThenVarA | ElseVarA, ElseVarA
    | EmptyA, EmptyA | ThenA, ThenA | ElseA, ElseA -> true
    | LambdaA (s1, t1), LambdaA (s2, t2) ->
      equiv s1 s2 && equals t1 t2
    | InterA (i1,i1',_), InterA (i2,i2',_) ->
      List.for_all2 (fun (a,_,_) (b,_,_) -> equals_a a b) i1 i2 &&
      List.for_all2 equals_a i1' i2'
    | _, _ -> false
  and equals e1 e2 =
    let equals_union (ex1,d1,u1) (ex2,d2,u2) =
      let aux (s1, t1) (s2, t2) =
        equiv s1 s2 && equals t1 t2
      in
      List.for_all2 equiv u1 u2 &&
      List.for_all2 aux ex1 ex2 &&
      List.for_all2 aux d1 d2
    in
    match e1, e2 with
    | Infer, Infer | Typ, Typ | Untyp, Untyp -> true
    | Skip t1, Skip t2 -> equals t1 t2
    | TrySkip t1, TrySkip t2 -> equals t1 t2
    | Propagate (a1, envs1, u1), Propagate (a2, envs2, u2) ->
      let aux (env1,i1) (env2,i2) = i1=i2 && Env.equiv env1 env2 in  
      List.for_all2 aux envs1 envs2 &&
      equals_a a1 a2 && equals_union u1 u2
    | Keep (a1, u1), Keep (a2, u2) ->
      equals_a a1 a2 && equals_union u1 u2
    | TryKeep (a1, t1, t1'), TryKeep (a2, t2, t2') ->
      equals_a a1 a2 && equals t1 t2 && equals t1' t2'
    | Inter (i1,i1',_), Inter (i2,i2',_) ->
      List.for_all2 (fun (a,_,_) (b,_,_) -> equals a b) i1 i2 &&
      List.for_all2 equals i1' i2'
    | _, _ -> false

  let equals t1 t2 =
    try equals t1 t2 with Invalid_argument _ -> false
  let equals_a t1 t2 =
    try equals_a t1 t2 with Invalid_argument _ -> false  
end
