(* TODO: Why is it so long on typeof? *)

  let typeof x =
    if x is String then "String"
    else if x is Char then "Char"
    else if x is Int then "Number"
    else if x is Bool then "Boolean"
    else if x is Unit|Nil then "Nil"
    else "Object"
  
  let test_typeof y =
    if typeof y is "Boolean" then lnot y else false  

(* TODO: Why is it so long on test_1? *)

let lnot = fun a ->
  if a is True then false else true

let lor = fun a -> fun b ->
  if a is False then if b is False then false else true else true

let land = fun a -> fun b ->
  if a is True then if b is False then false else true else false

let test_1 = fun x -> fun y ->
  if land (lor x (lnot x)) (lor (lnot y) y) then true else false

(* TODO: Why is it failing on the fixpoint combinator? *)

(*
let fixpoint = fun f ->
  let delta = fun x ->
     f ( fun  v -> ( x x v ))
   in delta delta
*)