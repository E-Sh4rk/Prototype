open Types.Base
open Types.Tvar
open Types.Additions

module PartialAnnot = struct
  type split =
  | SInfer of typ * t
    | SProp of typ * t
    | SExpl of typ * t
    | SDone of typ * t
    | SUnr of typ
  [@@deriving show]
  and union = split list
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
    | LambdaA of typ * t
    | InterA of a inter
  [@@deriving show]
  and t =
    | Infer | Typ | Untyp
    | Keep of (a * union)
    | Skip of t * bool (* Already typed *)
    | TryKeep of (a * t * t)
    | Inter of t inter
  [@@deriving show]

  let apply_subst_branch f s (a, s', t) =
    (f s a, s' (* The subst never change *), apply_subst_simplify s t)
  let rec apply_subst_union s lst =
    let aux split = match split with
      | SInfer (ty, t) -> SInfer (apply_subst_simplify s ty, apply_subst s t)
      | SProp (ty, t) -> SProp (apply_subst_simplify s ty, apply_subst s t)
      | SExpl (ty, t) -> SExpl (apply_subst_simplify s ty, apply_subst s t)
      | SDone (ty, t) -> SDone (apply_subst_simplify s ty, apply_subst s t)
      | SUnr ty -> SUnr (apply_subst_simplify s ty)
    in
    List.map aux lst
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
    | Inter i -> Inter (apply_subst_inter s i)

  let effective_splits union =
    union |> List.filter_map (function
    | SUnr _ -> None
    | SDone (s, _) | SExpl (s, _) | SProp (s, _) | SInfer (s, _) -> Some s
    )
  let effective_splits_annots union =
    union |> List.filter_map (function
    | SUnr _ -> None
    | SDone (_, pannot) | SExpl (_, pannot) | SProp (_, pannot) | SInfer (_, pannot) -> Some pannot
    )
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
      | EmptyA | ThenA | ElseA
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