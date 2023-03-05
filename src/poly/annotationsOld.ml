open Types.Base
open Types.Tvar
open Types.Additions

module PartialAnnot = struct
  type branches = (typ*t) list
  [@@deriving show]

  and splits = (typ*t) list
  [@@deriving show]

  and a =
  | InferA of infer_state | PartialA
  | LambdaA of branches list * branches
  [@@deriving show]

  and t =
  | Infer | Partial
  | Keep of (a * splits)
  | Skip of t
  | KeepSkip of (a * splits * t)
  [@@deriving show]

  and infer_state = IMain | IThen | IElse
  [@@deriving show]

  let rec apply_subst_branches s lst =
    let aux (ty, t) = (apply_subst_simplify s ty, apply_subst s t) in
    List.map aux lst
  and apply_subst_splits s lst =
    let aux (ty, t) = (ty, apply_subst s t) in
    List.map aux lst
  and apply_subst_a s a = match a with
  | InferA s -> InferA s
  | PartialA -> PartialA
  | LambdaA (b1, b2) ->
    LambdaA (List.map (apply_subst_branches s) b1, apply_subst_branches s b2)
  and apply_subst s t =
    if Subst.is_identity s then t
    else match t with
    | Infer -> Infer
    | Partial -> Partial
    | Keep (a, b) ->
      Keep (apply_subst_a s a, apply_subst_splits s b)
    | Skip t -> Skip (apply_subst s t)
    | KeepSkip (a, b, t) ->
      KeepSkip (apply_subst_a s a, apply_subst_splits s b, apply_subst s t)
end

module FullAnnot = struct
  type inst = Subst.t list
  [@@deriving show]
  type renaming = Subst.t
  [@@deriving show]
  type generalization = Subst.t
  [@@deriving show]
  type branches = (typ*t) list
  [@@deriving show]
  and grouped_branches = (branches * generalization) list
  [@@deriving show]
  and splits = (typ*t) list
  [@@deriving show]
  and a =
    | ConstA | AliasA | LetA
    | AbstractA of generalization
    | LambdaA of grouped_branches
    | PairA of renaming * renaming
    | AppA of inst * inst
    | ProjA of inst
    | EmptyA of inst | ThenA | ElseA
    | RecordUpdateA of inst * (renaming option)
    | ConstrA of inst
  [@@deriving show]
  and t =
    | BVar of renaming
    | Keep of (a * typ option (* (optimisation) *) * splits)
    | Skip of t
  [@@deriving show]
end