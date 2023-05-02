open Types.Base
open Types.Tvar
open Common

module PartialAnnot : sig
    type union_expl = (typ * t) list
    and union_prop = (typ * Env.t list * t) list
    and union_infer = union_expl
    and union_done = (typ * t) list
    and union_unr = typ list
    and union = union_expl * union_prop * union_infer * union_done * union_unr
    and 'a annotated_branch = 'a * Subst.t * typ
    and 'a inter = ('a annotated_branch) list (* Explored *)
                 * ('a annotated_branch) list (* Pending *)
                 * (  bool (* Typing finished? *)
                    * bool (* User defined *))
    and a =
        | InferA | TypA | UntypA
        | EmptyA | ThenA | ElseA (* NOTE: not in the paper, small optimisation *)
        | LambdaA of typ * t
        | InterA of a inter
    and t =
        | Infer | Typ | Untyp
        | Keep of a * union
        | Skip of t * bool (* Already typed *)
        | TryKeep of a * t * t
        | Inter of t inter

    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit

    val apply_subst_a : Subst.t -> a -> a
    val apply_subst : Subst.t -> t -> t

    val effective_splits : union -> typ list
    val effective_splits_annots : union -> (typ * t) list
end

module FullAnnot : sig
    type 'a inter = 'a list
    type inst = Subst.t list
    type renaming = Subst.t
    type union = (typ * t) list * inst
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
    and t =
        | BVar of renaming
        | Keep of a * union
        | Skip of t
        | Inter of t inter

    val pp_inst : Format.formatter -> inst -> unit
    val pp_renaming : Format.formatter -> renaming -> unit
    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit
end