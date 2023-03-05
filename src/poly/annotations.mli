open Types.Base
open Types.Tvar

module PartialAnnot : sig
    type splits = (typ*t) list
    and 'a annotated_branch = 'a * Subst.t * typ
    and 'a inter = ('a annotated_branch) list (* Explored *) * ('a annotated_branch) list (* Pending *)
    and a =
        | InferA of infer_state | TypA | UntypA
        | LambdaA of typ * t
        | InterA of a inter
    and t =
        | Infer | Typ | Untyp
        | Keep of (a * splits)
        | Skip of t
        | KeepSkip of (a * splits * t)
        | Inter of t inter
    and infer_state = IMain | IThen | IElse

    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit

    val apply_subst_a : Subst.t -> a -> a
    val apply_subst : Subst.t -> t -> t
end

module FullAnnot : sig
    type 'a inter = 'a list
    type inst = Subst.t list
    type renaming = Subst.t
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
    and t =
        | BVar of renaming
        | Keep of a * (typ * t) list
        | Skip of t
        | Inter of t inter

    val pp_inst : Format.formatter -> inst -> unit
    val pp_renaming : Format.formatter -> renaming -> unit
    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit
end