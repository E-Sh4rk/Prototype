
(* TODO: Investigate weird union for foo_highord1_wrong *)

let foo_highord1_wrong = fun f -> f 3                                

let foo_highord2_wrong = fun f -> (f 3 , f true)                           
                           
let foo_highord3_wrong = fun f -> f (f 3)                           

let foo_highord4_wrong = fun f -> (f f) 3                           

let foo_highord5_wrong = fun f -> (f (f 3) , f true)                           

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
