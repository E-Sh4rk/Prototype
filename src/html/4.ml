(* Code 4 from the submission *)

let strlen = <(String -> Int)>
let (+) = <(Int -> Int -> Int)>

let and_ = fun x -> fun y ->
  if x is True then if y is True
  then true else false
  else false

let is_int = fun x ->
  if x is Int then true else false  

let is_string = fun x ->
  if x is String then true else false  
  
let example6_wrong =
  fun (x : Int | String ) -> fun ( y : Any ) ->
  if and_ (is_int x) (is_string y) is True 
  then x + (strlen y) else strlen x

let example6_ok =
  fun x -> fun y ->
  if and_ (is_int x) (is_string y) is True 
  then x + (strlen y) else strlen x
