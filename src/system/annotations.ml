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

module PartialAnnot = struct
  type union_expl = (typ * t) list
  [@@deriving show]
  and union_done = (typ * t) list
  [@@deriving show]
  and union = union_expl * union_done
  [@@deriving show]
  and 'a pending_branch = 'a * Domains.t * bool
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
    | EmptyA | ThenA | ElseA
    | LambdaA of typ * t
    | InterA of a inter
  [@@deriving show]
  and t =
    | Infer | Typ | Untyp
    | Keep of a * union
    | Skip of t
    | TrySkip of t
    | TryKeep of a * t * t
    | Propagate of a * Env.t list * union
    | Inter of t inter
  [@@deriving show]

  let tvars_branch f (a, _, _) = f a
  let rec tvars_union (e,d) =
    let aux2 (ty, t) = TVarSet.union (vars ty) (tvars t) in
    TVarSet.union_many ((List.map aux2 e)@(List.map aux2 d))
  and tvars_inter_a (a, b, _) =
    TVarSet.union
      (List.map (tvars_branch tvars_a) a |> TVarSet.union_many)
      (List.map tvars_a b |> TVarSet.union_many)
  and tvars_inter (a, b, _) =
    TVarSet.union
      (List.map (tvars_branch tvars) a |> TVarSet.union_many)
      (List.map tvars b |> TVarSet.union_many)
  and tvars_a a = match a with
  | InferA | TypA | UntypA | ThenVarA | ElseVarA
  | EmptyA | ThenA | ElseA -> TVarSet.empty
  | LambdaA (ty, t) -> TVarSet.union (vars ty) (tvars t)
  | InterA i -> tvars_inter_a i
  and tvars t =
    match t with
    | Infer | Typ | Untyp -> TVarSet.empty
    | Keep (a, b) -> TVarSet.union (tvars_a a) (tvars_union b)
    | Skip t | TrySkip t -> tvars t
    | TryKeep (a, t1, t2) ->
      TVarSet.union_many [tvars_a a ; tvars t1 ; tvars t2]
    | Propagate (a, envs, t) ->
      TVarSet.union_many [tvars_a a ; List.map Env.tvars envs |> TVarSet.union_many ; tvars_union t]
    | Inter i -> tvars_inter i

  let apply_subst_branch f s (a, d, b) = (f s a, d, b)
  let rec apply_subst_union s (e,d) =
    let apply = apply_subst_simplify s in
    let aux2 (ty, t) = (apply ty, apply_subst s t) in
    (List.map aux2 e, List.map aux2 d)
  and apply_subst_inter_a s (a, b, flags) =
    (List.map (apply_subst_branch apply_subst_a s) a,
    List.map (apply_subst_a s) b,
    flags)
  and apply_subst_inter s (a, b, flags) =
    (List.map (apply_subst_branch apply_subst s) a,
    List.map (apply_subst s) b,
    flags)
  and apply_subst_a s a = match a with
  | InferA -> InferA
  | TypA -> TypA
  | UntypA -> UntypA
  | ThenVarA -> ThenVarA | ElseVarA -> ElseVarA
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
    | Skip t -> Skip (apply_subst s t)
    | TrySkip t -> TrySkip (apply_subst s t)
    | TryKeep (a, t1, t2) ->
      TryKeep (apply_subst_a s a, apply_subst s t1, apply_subst s t2)
    | Propagate (a, envs, t) ->
      Propagate (apply_subst_a s a, List.map (Env.apply_subst s) envs, apply_subst_union s t)
    | Inter i -> Inter (apply_subst_inter s i)
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
      | Keep of a * union
      | Skip of t
      | Inter of t inter
  [@@deriving show]

  (* let rec apply_subst_union s lst =
    lst |> List.map (fun (ty, t) -> (apply_subst_simplify s ty, apply_subst s t))
  and apply_subst_a s a =
    let compose = Subst.compose_restr s in
    match a with
    | ConstA -> ConstA | AliasA -> AliasA | LetA -> LetA | AbstractA -> AbstractA
    | LambdaA (ty, t) -> LambdaA (apply_subst_simplify s ty, apply_subst s t)
    | PairA (r1, r2) -> PairA (compose r1, compose r2)
    | AppA (ss1, ss2) -> AppA (List.map compose ss1, List.map compose ss2)
    | ProjA ss -> ProjA (List.map compose ss)
    | EmptyA ss -> EmptyA (List.map compose ss)
    | ThenA ss -> ThenA (List.map compose ss)
    | ElseA ss -> ElseA (List.map compose ss)
    | RecordUpdateA (ss, ro) -> RecordUpdateA (List.map compose ss, Option.map compose ro)
    | ConstrA ss -> ConstrA (List.map compose ss)
    | InterA i -> InterA (List.map (apply_subst_a s) i)
  and apply_subst s t =
    if Subst.is_identity s then t
    else match t with
    | BVar r -> BVar (Subst.compose_restr s r)
    | Keep (a, b) -> Keep (apply_subst_a s a, apply_subst_union s b)
    | Skip t -> Skip (apply_subst s t)
    | Inter i -> Inter (List.map (apply_subst s) i) *)
end