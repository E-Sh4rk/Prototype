(* Code 5 from the submission *)

let (<) = <( Int -> Int -> Bool )>
let (=) = <( Any -> Any -> Bool )>

let detailed_ex =
  fun (a : ( Int -> ( Int | Bool ))
  |( Int , ( Int | Bool ))) ->
  fun (n : Int ) ->
  if a is ( Int , Int ) then ( fst a )=( snd a )
  else if a is ( Any , Any ) then snd a
  else if (a n) is Int then ( a n ) < 42
  else a n