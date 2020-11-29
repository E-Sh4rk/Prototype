(*open Cduce
open Variable
open Nf_ast
open Types_additions*)

exception Ill_typed of Position.t list * string

let typeof_a (*pos tenv env a*) _ _ _ _ =
  failwith "Not implemented"

and typeof (*tenv env e *) _ _ _=
  failwith "Not implemented"

and refine_a (*pos ~backward tenv env a t*) _ ~backward _ _ _ _ =
  ignore backward ;
  failwith "Not implemented"

and refine (*~backward tenv env e t*) ~backward _ _ _ _ =
  ignore backward ;
  failwith "Not implemented"