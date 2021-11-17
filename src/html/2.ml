(* Code 2 from the paper *)

type Falsy = False | "" | 0
type Truthy = ~Falsy

let not_ = fun x ->
  if x is Truthy then false else true

let to_Bool = fun x -> not_ (not_ x)

let and_ = fun x -> fun y ->
  if x is Truthy then to_Bool y else false

let or_ = fun x -> fun y ->
  not_ (and_ (not_ x) (not_ y))




