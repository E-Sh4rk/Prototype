open Types.Base
open Types.Additions
open Annotations

val infer : type_env -> Env.t -> Msc.e -> FullAnnot.t
val typeof_simple : type_env -> Env.t -> Msc.e -> typ
