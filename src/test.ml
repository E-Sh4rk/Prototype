
let a = <(Int -> (Int|Bool)) | ( Int, (Int|Bool))>
let n = <Int>
let (=) = <Any->Any->Bool>

let example_new_paper =
  if a is (Int,Int) then ((fst a)=(snd a))
  else if a is (Any,Any) then (snd a)
  else if (a n) is Int then ((a n) = 42)
  else (a n)

(* We add explicit lambda abstractions *)
debug let example_new1 =
fun (a : (Int -> (Int|Bool)) | ( Int, (Int|Bool))) ->
fun n ->
  if a is (Int,Int) then ((fst a)=(snd a))
  else if a is (Any,Any) then (snd a)
  else if (a n) is Int then ((a n) =  42)
  else (a n)

(* Très intéressant ... il trouve ce type surchargé

  ((Int -> Bool | Int) -> Int -> Bool)
& ((Int,Bool | Int) -> Any -> Bool) 

  c-a-d ca marche avec Any seulement si c'est un produit
*)

