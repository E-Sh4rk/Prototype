
let idb = fun (b : Bool) -> b
let rand = fun (a : Unit) -> idb true
let bool = rand ()

let test = if bool is True then true else false

let lnot = fun (a : Any) ->
  if a is True then false else true

let lor = fun (a : Any) -> fun (b : Any) ->
  if a is False then if b is False then false else true else true

let land = fun (a : Any) -> fun (b : Any) ->
  if a is True then if b is False then false else true else false

let test = fun (x:Any) -> fun (y:Any) ->
  if land (lor x (lnot x)) (lor (lnot y) y) then true else false

let test =
  let a = rand () in
  fun (b:Bool) -> lor b a


