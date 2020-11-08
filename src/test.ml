
let not = fun (a : Any) ->
  if a is True then false else true

let or = fun (a : Any) -> fun (b : Any) ->
  if a is False then if b is False then false else true else true

let test = fun (x:Any) ->
  if or x (not x) is True then true else false
