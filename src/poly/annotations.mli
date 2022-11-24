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
    (* TODO *)
end