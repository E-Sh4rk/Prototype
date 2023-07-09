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
  let inhabitant = mk_atom "inhabitant"
  (* (used for convenience, in order to encode several constraints in a product) *)
  let type_for dom2 env =
    dom2 |> List.fold_left (fun acc v ->
      let t = Env.find v env |> cup inhabitant in
      mk_times (cons acc) (cons t)
    ) any
  let covers t1 t2 =
    t2 |> List.for_all (fun env2 ->
      let dom2 = Env.domain env2 |> VarSet.of_list in
      let has_same_vars env =
        let dom = Env.domain env |> VarSet.of_list in
        VarSet.equal dom dom2
      in
      let type_for = type_for (VarSet.elements dom2) in
      let b = type_for env2 in
      let a = t1 |> List.filter has_same_vars |> List.map type_for
        |> List.filter (fun a -> subtype_poly a b) |> disj_o in
      supertype_poly a b
    )
  let enter_lambda _ _ (*env' t*) =
    [] (* NOTE: it is better to reset the domains...
       otherwise tallying instances may become too complex. *)
    (* let env' = env' |> Env.filter (fun v _ -> Variable.is_lambda_var v) in
    let dom' = Env.domain env' |> VarSet.of_list in
    let type_for = type_for (VarSet.elements dom') in
    let b = type_for env' in
    t |> List.filter (fun env ->
      let dom = Env.domain env |> VarSet.of_list in
      if VarSet.diff dom' dom |> VarSet.is_empty
      then let a = type_for env in subtype_poly a b
      else false
    ) *)
  let empty = []
  let cup = (@)
  let singleton e = add empty e
end

module PartialAnnot = struct
  type union_expl = (typ * t) list
  [@@deriving show]
  and union_prop = (typ * Env.t list * t) list
  [@@deriving show]
  and union_done = (typ * t) list
  [@@deriving show]
  and union = union_prop * union_expl * union_done
  [@@deriving show]
  and 'a annotated_branch = 'a * Domains.t * bool
  [@@deriving show]
  and 'a inter = ('a annotated_branch) list (* Explored *)
               * ('a annotated_branch) list (* Pending *)
               * (  bool (* Typing finished? *)
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
    | Propagate of a * t * Env.t list
    | Inter of t inter
  [@@deriving show]

  let tvars_branch f (a, _, _) = f a
  let rec tvars_union (p,e,d) =
    let aux2 (ty, t) = TVarSet.union (vars ty) (tvars t) in
    let aux3 (ty, env, t) = TVarSet.union_many [vars ty ; List.map Env.tvars env |> TVarSet.union_many ; tvars t] in
    TVarSet.union_many ((List.map aux3 p)@(List.map aux2 e)@(List.map aux2 d))
  and tvars_inter_a (a, b, _) =
    TVarSet.union
      (List.map (tvars_branch tvars_a) a |> TVarSet.union_many)
      (List.map (tvars_branch tvars_a) b |> TVarSet.union_many)
  and tvars_inter (a, b, _) =
    TVarSet.union
      (List.map (tvars_branch tvars) a |> TVarSet.union_many)
      (List.map (tvars_branch tvars) b |> TVarSet.union_many)
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
    | Propagate (a, t, envs) ->
      TVarSet.union_many [tvars_a a ; tvars t ; List.map Env.tvars envs |> TVarSet.union_many ]
    | Inter i -> tvars_inter i

  let apply_subst_branch f s (a, d, b) = (f s a, d, b)
  let rec apply_subst_union s (p,e,d) =
    let apply = apply_subst_simplify s in
    let aux2 (ty, t) = (apply ty, apply_subst s t) in
    let aux3 (ty, env, t) = (apply ty, List.map (Env.apply_subst s) env, apply_subst s t) in
    (List.map aux3 p, List.map aux2 e, List.map aux2 d)
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
    | Propagate (a, t, envs) ->
      Propagate (apply_subst_a s a, apply_subst s t, List.map (Env.apply_subst s) envs)
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
end