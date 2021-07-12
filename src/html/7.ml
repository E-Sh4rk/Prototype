(************************************************
  For x of type ¬Int the system realizes that if
  snd (f x) is of type Int the fst (f x) must
  be of type  ¬Int. The case for x of type Int
  is straightforward.
 ************************************************)

let f = <(Any\Int -> (Any\Int, Any\Int) ) & ( Int -> (Int,Int) )>

let two_steps =
  fun x ->
    if snd (f x) is Int
    then (fst (f x))
    else x


(***********************************************
 Type annotations written by the programmer are
 directives that must be checked as they are
 and thus cannot be refined.
 λx:Any.(x+1) is ill typed because cannot be
 applied to "Any" argument but just to integers
************************************************)

(* declare "+" as an infix function on integers *)  
let (+) = <Int -> Int -> Int>
                           
let succ_ok = fun x -> x + 1

let succ_fail = fun (x : Any) -> x + 1


(***********************************************
 A complicated example of inference where
 the inferred type is
 ( Int  ->  (String->String) & (Int -> Int)) &
 ( ¬Int ->  Any -> Int )
 and tells us precisely how the type of the
 second argument depends on the type of the
 first argument
************************************************)

let (+) = <Int -> Int -> Int>
let concat = < String -> String -> String>
let to_string = <Any -> String>

let add x y =
    if x is Int then
        if y is Int then x + y
        else concat (to_string x) y
    else if y is String then concat (to_string x) y
    else concat (to_string x) (to_string y)
