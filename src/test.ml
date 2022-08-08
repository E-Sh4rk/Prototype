let bool = <Bool>


(*************************************************
*                                                *
*           IMPLICITLY ANNOTATED VERSIONS        *
*                                                *
**************************************************)   


let lnot = fun a ->
  if a is True then false else true

let lor = fun a -> fun b ->
  if a is False then if b is False then false else true else true

let land = fun a -> fun b ->
  if a is True then if b is False then false else true else false

let test_1 = fun x -> fun y ->
  if land (lor x (lnot x)) (lor (lnot y) y) then true else false

let is_int = fun x -> if x is Int then true else false

let is_bool = fun x -> if x is Bool then true else false

