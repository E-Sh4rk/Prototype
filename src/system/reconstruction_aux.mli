open Types.Base
open Types.Tvar
open Types.Additions
open Parsing.Variable
open Msc
open Annotations

module Make () : sig
    val init_fv_htbl : e -> unit
    val fv_def : Variable.t -> VarSet.t

    val replace_vars : typ -> TVarSet.t -> TVar.t -> Subst.t
    val approximate_app : infer:bool -> typ -> typ -> TVar.t -> Subst.t list

    val infer_poly_a : Variable.t -> type_env -> Env.t -> PartialAnnot.a ->
        a -> FullAnnot.a_cached
    val infer_poly : type_env -> Env.t -> PartialAnnot.t -> e -> FullAnnot.t_cached
end