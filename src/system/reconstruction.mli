open Types.Base
open Types.Additions
open Annotations

module Make () : sig
    val caching_status : unit -> bool
    val set_caching_status : bool -> unit

    val infer : type_env -> Env.t -> Msc.e -> FullAnnot.t_cached
    val typeof_simple : type_env -> Env.t -> Msc.e -> typ
end
