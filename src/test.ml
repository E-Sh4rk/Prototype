
(*let test =
  let a = 0 in
  if a is 1 then 0 else 0

let not = fun (a : Any) ->
  if a is True then false else true*)

let or = fun (a : Any) -> fun (b : Any) ->
  if a is False then if b is False then false else true else true
