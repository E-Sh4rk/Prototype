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

module FullAnnot : sig
    type cache = { mutable typ: typ option }
    type 'a inter = 'a list
    type inst = Subst.t list
    type renaming = Subst.t
    type union = (typ * t_cached) list
    and a =
        | ConstA | AliasA | LetA | AbstractA
        | LambdaA of typ * t_cached
        | PairA of renaming * renaming
        | AppA of inst * inst
        | ProjA of inst
        | EmptyA of inst | ThenA of inst | ElseA of inst
        | RecordUpdateA of inst * (renaming option)
        | ConstrA of inst
        | InterA of a_cached inter
    and t =
        | BVar of renaming
        | Keep of a_cached * union * inst
        | Skip of t_cached
        | Inter of t_cached inter
    and a_cached = a * cache
    and t_cached = t * cache

    val pp_inst : Format.formatter -> inst -> unit
    val pp_renaming : Format.formatter -> renaming -> unit
    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit
    val pp_a_cached : Format.formatter -> a_cached -> unit
    val pp_t_cached : Format.formatter -> t_cached -> unit

    val init_cache : unit -> cache
end

module PartialAnnot : sig
    type def_cache = { prev_typ: typ option }
    type 'a cache = { env_changed:bool ; annot_changed:bool ; prev_fa:'a option }
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
        | LambdaA of typ * t_cached * def_cache
        | InterA of a_cached inter
    and t =
        | Infer | Typ | Untyp
        | Keep of a_cached * union * def_cache
        | Skip of t_cached
        | TrySkip of t_cached
        | TryKeep of a_cached * t_cached * t_cached
        | Propagate of a_cached * (Env.t * int) list * union * def_cache
        | Inter of t_cached inter
    and a_cached = a * FullAnnot.a_cached cache
    and t_cached = t * FullAnnot.t_cached cache

    val pp_a : Format.formatter -> a -> unit
    val pp : Format.formatter -> t -> unit
    val pp_a_cached : Format.formatter -> a_cached -> unit
    val pp_t_cached : Format.formatter -> t_cached -> unit

    val apply_subst_a : Subst.t -> a_cached -> a_cached
    val apply_subst : Subst.t -> t_cached -> t_cached

    val init_cache : 'a cache
    val init_def_cache : def_cache
    val def_cache : typ -> def_cache
end
