open Types.Base
open Types.Tvar

module PartialAnnot : sig
    type branches = (typ*t) list
    and splits = (typ*t) list
    and a =
        | InferA of infer_state | PartialA
        | LambdaA of
            branches list (* Fully Explored, grouped by similarity *) * branches (* Remaining *)
    and t =
        | Infer | Partial
        | Keep of (a * splits)
        | Skip of t
        | KeepSkip of (a * splits * t)
    and infer_state = IMain | IThen | IElse

    val pp_branches : Format.formatter -> branches -> unit
    val pp_splits : Format.formatter -> splits -> unit
    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit

    val apply_subst_branches : Subst.t -> branches -> branches
    val apply_subst_splits : Subst.t -> splits -> branches
    val apply_subst_a : Subst.t -> a -> a
    val apply_subst : Subst.t -> t -> t
end

module FullAnnot : sig
    type inst = Subst.t list
    type renaming = Subst.t
    type generalization = Subst.t
    type branches = (typ*t) list
    and grouped_branches = (branches * generalization) list
    and splits = (typ*t) list
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
    and t =
        | BVar of renaming
        | Keep of (a * typ option (* (optimisation) *) * splits)
        | Skip of t

    val pp_inst : Format.formatter -> inst -> unit
    val pp_renaming : Format.formatter -> renaming -> unit
    val pp_generalization : Format.formatter -> generalization -> unit
    val pp_branches : Format.formatter -> branches -> unit
    val pp_grouped_branches : Format.formatter -> grouped_branches -> unit
    val pp_splits : Format.formatter -> splits -> unit
    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit
end