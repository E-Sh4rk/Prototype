open Types.Base
open Types.Tvar
open Parsing.Variable

module Domains : sig
    type t
    val empty : t
    val singleton : Env.t -> t
    val cup : t -> t -> t
    val covers : t -> t -> bool
    val enter_lambda : Env.t -> t -> t
    val pp : Format.formatter -> t -> unit
end

module FullAnnot : sig
    (* TODO: add cache *)
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
        | Keep of a * union * inst
        | Skip of t
        | Inter of t inter

    val pp_inst : Format.formatter -> inst -> unit
    val pp_renaming : Format.formatter -> renaming -> unit
    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit
end

module PartialAnnot : sig
    type 'a cache = { depends_on:VarSet.t ; annot_changed:bool ;
        prev_typ:typ option ; prev_fa:'a option }
    type union_expl = (typ * t_cached) list
    and union_done = (typ * t_cached) list
    and union_unr = typ list
    and union = union_expl * union_done * union_unr
    and 'a pending_branch =
        'a
        * Domains.t (* Domains involved (used to prune branches) *)
        * bool (* Low priority default: type only if no other branch is typeable *)
    and 'a inter = ('a pending_branch) list (* Pending *)
                 * 'a list (* Explored *)
                 * (Domains.t (* Explored domains *)
                    * bool (* Typing finished? *)
                    * bool (* User defined *))
    and a =
        | InferA | TypA | UntypA
        | ThenVarA | ElseVarA
        | EmptyA | ThenA | ElseA (* NOTE: not in the paper, small optimisation *)
        | LambdaA of typ * t_cached
        | InterA of a_cached inter
    and t =
        | Infer | Typ | Untyp
        | Keep of a_cached * union
        | Skip of t_cached
        | TrySkip of t_cached
        | TryKeep of a_cached * t_cached * t_cached
        | Propagate of a_cached * (Env.t * union) list * union
        | Inter of t_cached inter
    and a_cached = a * FullAnnot.a cache
    and t_cached = t * FullAnnot.t cache

    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit
    val pp_a_cached : Format.formatter -> a_cached -> unit
    val pp_t_cached : Format.formatter -> t_cached -> unit

    val apply_subst_a : Subst.t -> a_cached -> a_cached
    val apply_subst : Subst.t -> t_cached -> t_cached

    val init_cache_a : Msc.a -> FullAnnot.a cache
    val init_cache : Msc.e -> FullAnnot.t cache
    val init_cache' : VarSet.t -> 'a cache
end
