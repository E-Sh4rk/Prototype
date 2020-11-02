open Cduce
open Variable

type env = typ VarMap.t
let empty_env = VarMap.empty

let is_bottom env =
    let is_bottom (_,v) = is_empty v in
    List.exists is_bottom (VarMap.bindings env)

let add_to_env v t env = VarMap.add v t env

exception Ill_typed of Position.t * string

let typeof (*tenv env e*) _ _ _ =
  failwith "TODO"
