open Types.Base
open Types.Additions
open Annotations
open Parsing.Variable

exception Untypeable of Position.t list * string

val typeof_const_atom : type_env -> Parsing.Ast.const -> typ
val typeof : type_env -> Env.t -> FullAnnot.t -> Msc.e -> typ
val typeof_a : Variable.t -> type_env -> Env.t -> FullAnnot.a -> Msc.a -> typ
val typeof_nofail : type_env -> Env.t -> FullAnnot.t -> Msc.e -> typ
val typeof_a_nofail : Variable.t -> type_env -> Env.t -> FullAnnot.a -> Msc.a -> typ
