open Types.Base
open Types.Tvar

module PartialAnnot : sig
    type branches = (typ*t) list
    and a =
        | InferA | PartialA
        | LambdaA of branches (* Fully Explored *) * branches (* Remaining *)
    and t =
        | Infer | Partial
        | Keep of (a * branches)
        | Skip of t
        | KeepSkip of (a * branches * t)

    val pp_branches : Format.formatter -> branches -> unit
    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit

    val apply_subst_branches : Subst.t -> branches -> branches
    val apply_subst_a : Subst.t -> a -> a
    val apply_subst : Subst.t -> t -> t
end

module FullAnnot : sig
    type inst = Subst.t list
    type renaming = Subst.t
    type generalization = Subst.t
    type branches = (typ*t) list
    and a =
        | ConstA | AliasA
        | LambdaA of branches
        | PairA of renaming * renaming
        | AppA of inst (* NOTE: different from the paper *)
        | ProjA of inst
        | EmptyA of inst
        | ThenA of renaming
        | ElseA of renaming
        | RecordUpdateA of inst * (renaming option)
    and t =
        | BVar of renaming
        | Keep of (a * generalization * typ (* (optimisation) *) * branches)
        | Skip of t

    val pp_inst : Format.formatter -> inst -> unit
    val pp_renaming : Format.formatter -> renaming -> unit
    val pp_generalization : Format.formatter -> generalization -> unit
    val pp_branches : Format.formatter -> branches -> unit
    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit
end