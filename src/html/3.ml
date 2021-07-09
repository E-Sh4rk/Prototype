(* Code 3 from  the submission *)
let strlen = <(String -> Int)>
let (+) = <(Int -> Int -> Int)>


let and_ = fun x -> fun y ->
  if x is True then if y is True
  then true else false

let is_int = fun x ->
  if x is Int then true else false  

let example14 =
  fun input -> fun extra ->
  if and_ ( is_int input )
  ( is_int ( fst extra )) is True
  then input + ( fst extra )
  else if is_int ( fst extra ) is True
  then ( strlen input ) + ( fst extra )
  else 0