open Types.Base
open Types.Tvar

module Domains : sig
    type t
    val empty : t
    val singleton : Env.t -> t
    val cup : t -> t -> t
    val covers : t -> t -> bool
    val enter_lambda : Env.t -> t -> t
    val pp : Format.formatter -> t -> unit
end

module PartialAnnot : sig
    type union_expl = (typ * t) list
    and union_done = (typ * t) list
    and union = union_expl * union_done
    and 'a annotated_branch =
        'a
        * Domains.t (* Domains involved (used to prune branches) *)
        * bool (* Low priority default: type only if no other branch is typeable *)
    and 'a inter = ('a annotated_branch) list (* Explored *)
                 * ('a annotated_branch) list (* Pending *)
                 * (  bool (* Typing finished? *)
                    * bool (* User defined *))
    and a =
        | InferA | TypA | UntypA
        | ThenVarA | ElseVarA
        | EmptyA | ThenA | ElseA (* NOTE: not in the paper, small optimisation *)
        | LambdaA of typ * t
        | InterA of a inter
    and t =
        | Infer | Typ | Untyp
        | Keep of a * union
        | Skip of t
        | TrySkip of t
        | TryKeep of a * t * t
        | Propagate of a * Env.t list * union
        | Inter of t inter

    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit

    val tvars_a : a -> TVarSet.t
    val tvars : t -> TVarSet.t

    val apply_subst_a : Subst.t -> a -> a
    val apply_subst : Subst.t -> t -> t
end

module FullAnnot : sig
    type 'a inter = 'a list
    type inst = Subst.t list
    type renaming = Subst.t
    type union = (typ * t) list
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