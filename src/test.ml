
let bool = <Bool>

let test = if bool is True then true else false

let lnot = fun (a : Any) ->
  if a is True then false else true

let lor = fun (a : Any) -> fun (b : Any) ->
  if a is False then if b is False then false else true else true

let land = fun (a : Any) -> fun (b : Any) ->
  if a is True then if b is False then false else true else false

let test_1 = fun (x:Any) -> fun (y:Any) ->
  if land (lor x (lnot x)) (lor (lnot y) y) then true else false

let is_int = fun (x:Any) -> if x is Int then true else false
let is_bool = fun (x:Any) -> if x is Bool then true else false

let test_2 = fun (x:Any) ->
  lor (is_int x) (is_bool x)

let test_3 = fun (b:Bool) -> lor b bool

let bool_id = fun ((True -> True) & (False -> False)) x -> x
let succ = fun (x:Int) -> x

let test_4 = fun x -> if x is Bool then x else x

let test_5 = fun x -> if x is Bool then bool_id x else succ x

let custom_id = fun ((0--1 -> 0--1) & (1--2 -> 1--2)) x -> x

let test_6 = fun x ->
  let y = custom_id x in
  if y is 1 then true else false
