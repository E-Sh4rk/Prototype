(* 
   The function foo mixes inference of a precise domain, 
   of intersection types, of application of user-defined 
   functions that discriminate on type cases
 *)


let (+) = <(Int -> Int -> Int)>
let trim = <(String -> String)>

let or_ = fun x -> fun y ->
   if x is True then true else (if y is True then true else false) 

let is_int = fun x ->
  if x is Int then true else false

let is_func = fun x ->
  if x is (Empty -> Any) then true else false

let is_int_or_func = fun x -> or_ (is_int x) (is_func x)


let foo = fun x ->
   if (is_int_or_func x) is True then x+1 else trim x
