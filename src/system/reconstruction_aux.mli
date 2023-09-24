open Types.Base
open Types.Tvar
open Types.Additions
open Parsing.Variable
open Msc
open Annotations

module Make () : sig
    val init_fv_htbl : e -> unit
    val invalidate_cache : Variable.t -> e ->
        PartialAnnot.t_cached -> PartialAnnot.t_cached

    val replace_vars : typ -> TVarSet.t -> TVar.t -> Subst.t
    val approximate_app : infer:bool -> typ -> typ -> TVar.t -> Subst.t list

    val infer_poly_a : Variable.t -> type_env -> Env.t -> PartialAnnot.a_cached ->
        a -> PartialAnnot.a_cached * FullAnnot.a_cached
    val infer_poly : type_env -> Env.t -> PartialAnnot.t_cached ->
        e -> PartialAnnot.t_cached * FullAnnot.t_cached
end