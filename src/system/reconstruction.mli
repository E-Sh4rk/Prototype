open Types.Base
open Types.Additions
open Annotations

(**
The following functor implements the main reconstruction system.
It is presented as a functor in order to have more control on the memoisation.
*)

module Make () : sig
    (** Reconstruct annotations for an MSC form. *)
    val infer : type_env -> Env.t -> Msc.e -> FullAnnot.t_cached

    (** Reconstruct annotations for an MSC form, and return the
        associated type. *)
    val typeof_infer : type_env -> Env.t -> Msc.e -> typ
end
