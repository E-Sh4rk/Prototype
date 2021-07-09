(* Code 2 from the submission *)

let not_ = fun x ->
  if x is True then false else true

let and_ = fun x -> fun y ->
  if x is True then if y is True
  then true else false
  else false

let or_ = fun x -> fun y ->
  not_ ( and_ ( not_ x ) ( not_ y ))
