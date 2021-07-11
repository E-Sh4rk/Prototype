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