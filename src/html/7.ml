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
 are directives that must be checked as they are
 and thus cannot be refined.
 λx:Any.(x+1) is ill typed because cannot be
 applied to "Any" argument but just to integers
************************************************)

let succ_ok = fun x -> x + 1

let succ_fail = fun (x : Any) -> x + 1
