open Types.Base
open Types.Tvar
open Types.Additions

module PartialAnnot = struct
  type union_expl = (typ * t) list
  [@@deriving show]
  and union_prop = (typ * Env.t list * t) list
  [@@deriving show]
  and union_infer = union_expl
  [@@deriving show]
  and union_done = (typ * t) list
  [@@deriving show]
  and union_unr = typ list
  [@@deriving show]
  and union = union_infer * union_prop * union_expl * union_done * union_unr
  [@@deriving show]
  and 'a annotated_branch = 'a * Subst.t * typ
  [@@deriving show]
  and 'a inter = ('a annotated_branch) list (* Explored *)
               * ('a annotated_branch) list (* Pending *)
               * (  bool (* Typing finished? *)
                  * bool (* User defined *))
  [@@deriving show]
  and a =
    | InferA | TypA | UntypA
    | EmptyA | ThenA | ElseA
    | LambdaA of typ * t
    | InterA of a inter
  [@@deriving show]
  and t =
    | Infer | Typ | Untyp
    | Keep of a * union
    | Skip of t * bool (* Already typed *)
    | TryKeep of a * t * t
    | Propagate of a * t * Env.t list
    | Inter of t inter
  [@@deriving show]

  let tvars_branch f (a, _, t) =
    TVarSet.union (f a) (vars t)
  let rec tvars_union (i,p,e,d,u) =
    let aux1 ty = vars ty in
    let aux2 (ty, t) = TVarSet.union (vars ty) (tvars t) in
    let aux3 (ty, env, t) = TVarSet.union_many [vars ty ; List.map Env.tvars env |> TVarSet.union_many ; tvars t] in
    TVarSet.union_many ((List.map aux2 i)@(List.map aux3 p)@(List.map aux2 e)@(List.map aux2 d)@(List.map aux1 u))
  and tvars_inter_a (a, b, _) =
    TVarSet.union
      (List.map (tvars_branch tvars_a) a |> TVarSet.union_many)
      (List.map (tvars_branch tvars_a) b |> TVarSet.union_many)
  and tvars_inter (a, b, _) =
    TVarSet.union
      (List.map (tvars_branch tvars) a |> TVarSet.union_many)
      (List.map (tvars_branch tvars) b |> TVarSet.union_many)
  and tvars_a a = match a with
  | InferA | TypA | UntypA | EmptyA | ThenA | ElseA -> TVarSet.empty
  | LambdaA (ty, t) -> TVarSet.union (vars ty) (tvars t)
  | InterA i -> tvars_inter_a i
  and tvars t =
    match t with
    | Infer | Typ | Untyp -> TVarSet.empty
    | Keep (a, b) -> TVarSet.union (tvars_a a) (tvars_union b)
    | Skip (t, _) -> tvars t
    | TryKeep (a, t1, t2) ->
      TVarSet.union_many [tvars_a a ; tvars t1 ; tvars t2]
    | Propagate (a, t, envs) ->
      TVarSet.union_many [tvars_a a ; tvars t ; List.map Env.tvars envs |> TVarSet.union_many ]
    | Inter i -> tvars_inter i

  let apply_subst_branch f s (a, s', t) =
    (f s a, s' (* The subst never change, and only has polymorphic tvars *), apply_subst_simplify s t)
  let apply_env s env =
    let apply = apply_subst_simplify s in
    Env.bindings env
    |> List.map (fun (v,ty) -> (v, apply ty))
    |> Env.construct
  let rec apply_subst_union s (i,p,e,d,u) =
    let apply = apply_subst_simplify s in
    let aux1 ty = apply ty in
    let aux2 (ty, t) = (apply ty, apply_subst s t) in
    let aux3 (ty, env, t) = (apply ty, List.map (apply_env s) env, apply_subst s t) in
    (List.map aux2 i, List.map aux3 p, List.map aux2 e, List.map aux2 d, List.map aux1 u)
  and apply_subst_inter_a s (a, b, flags) =
    (List.map (apply_subst_branch apply_subst_a s) a,
    List.map (apply_subst_branch apply_subst_a s) b,
    flags)
  and apply_subst_inter s (a, b, flags) =
    (List.map (apply_subst_branch apply_subst s) a,
    List.map (apply_subst_branch apply_subst s) b,
    flags)
  and apply_subst_a s a = match a with
  | InferA -> InferA
  | TypA -> TypA
  | UntypA -> UntypA
  | EmptyA -> EmptyA | ThenA -> ThenA | ElseA -> ElseA
  | LambdaA (ty, t) -> LambdaA (apply_subst_simplify s ty, apply_subst s t)
  | InterA i -> InterA (apply_subst_inter_a s i)
  and apply_subst s t =
    if Subst.is_identity s then t
    else match t with
    | Infer -> Infer
    | Typ -> Typ
    | Untyp -> Untyp
    | Keep (a, b) -> Keep (apply_subst_a s a, apply_subst_union s b)
    | Skip (t, b) -> Skip (apply_subst s t, b)
    | TryKeep (a, t1, t2) ->
      TryKeep (apply_subst_a s a, apply_subst s t1, apply_subst s t2)
    | Propagate (a, t, envs) ->
      Propagate (apply_subst_a s a, apply_subst s t, List.map (apply_env s) envs)
    | Inter i -> Inter (apply_subst_inter s i)

  let unreachable_splits (_,_,_,_,u) = u
  let effective_splits (i,p,e,d,_) =
    (p |> List.map (fun (t,_,pa) -> (t,pa))) @ (i@e@d)
end

module FullAnnot = struct
  type 'a inter = 'a list
  [@@deriving show]
  type inst = Subst.t list
  [@@deriving show]
  type renaming = Subst.t
  [@@deriving show]
  type union = (typ * t) list * inst
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
      | Keep of a * union
      | Skip of t
      | Inter of t inter
  [@@deriving show]
end