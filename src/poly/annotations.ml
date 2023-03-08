open Types.Base
open Types.Tvar
open Types.Additions

module PartialAnnot = struct
  type splits = (typ*t) list
  [@@deriving show]
  and 'a annotated_branch = 'a * Subst.t * typ
  [@@deriving show]
  and 'a inter = ('a annotated_branch) list (* Explored *)
               * ('a annotated_branch) list (* Pending *)
  [@@deriving show]
  and a =
    | InferA of infer_state | TypA | UntypA
    | LambdaA of typ * t
    | InterA of a inter
  [@@deriving show]
  and t =
    | Infer | Typ | Untyp
    | Keep of (a * splits)
    | Skip of t
    | KeepSkip of (a * splits * t)
    | Inter of t inter
  [@@deriving show]
  and infer_state = IMain | IThen | IElse
  [@@deriving show]

  let apply_subst_branch f s (a, s', t) =
    (f s a, Subst.compose_restr s s', apply_subst_simplify s t)
  let rec apply_subst_splits s lst =
    let aux (ty, t) = (apply_subst_simplify s ty, apply_subst s t) in
    List.map aux lst
  and apply_subst_inter_a s (a, b) =
    (List.map (apply_subst_branch apply_subst_a s) a,
    List.map (apply_subst_branch apply_subst_a s) b)
  and apply_subst_inter s (a, b) =
    (List.map (apply_subst_branch apply_subst s) a,
    List.map (apply_subst_branch apply_subst s) b)
  and apply_subst_a s a = match a with
  | InferA st -> InferA st
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
    | Keep (a, b) -> Keep (apply_subst_a s a, apply_subst_splits s b)
    | Skip t -> Skip (apply_subst s t)
    | KeepSkip (a, b, t) ->
      KeepSkip (apply_subst_a s a, apply_subst_splits s b, apply_subst s t)
    | Inter i -> Inter (apply_subst_inter s i)
end

module FullAnnot = struct
  type 'a inter = 'a list
  [@@deriving show]
  type inst = Subst.t list
  [@@deriving show]
  type renaming = Subst.t
  [@@deriving show]
  type a =
      | ConstA | AliasA | LetA | AbstractA
      | LambdaA of typ * t
      | PairA of renaming * renaming
      | AppA of inst * inst
      | ProjA of inst
      | EmptyA of inst | ThenA | ElseA
      | RecordUpdateA of inst * (renaming option)
      | ConstrA of inst
      | InterA of a inter
  [@@deriving show]
  and t =
      | BVar of renaming
      | Keep of a * (typ * t) list
      | Skip of t
      | Inter of t inter
  [@@deriving show]
end