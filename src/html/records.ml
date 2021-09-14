(*     DISCLAIMER PRETTY PRINTING OF RECORD TYPES IS BAD    *)
   
(* Must fail because we do not know whether x has a field a *)

let records1_fail =
  fun (x:{..}) ->
    if {x with a=0} is {a=Int ..} then x.a else 0

(* Type inference  gives the correct type *)

let records1_ok =
  fun  x ->
    if {x with a=0} is {a=Int ..} then x.a else 0

(*
  The following ex works because x\a is of type  {b=Int ..} since
  it is of type {b=Int a=?Empty, ..} which is a subtype of
  {b=Int ..}
*)

let records2_ok =
  fun ({b = Int ..} -> Int) x ->
    if x\a is {b=Int ..} then x.b else x.c

(*
 Type inference gives a far more precise type equivalent to
 ({b = Int ..} -> Int) & ({b =? ¬Int c=Any ..} -> Any)
 *)
 
let records2_implicit =
  fun x ->
    if x\a is {b=Int ..} then x.b else x.c

(*
   The following ex fails since  x\a is of type  {b=Int a=?Empty ..}
   which is a subtype of {b=Int ..} = {b=Int a=?Any ..}
*)


let records3_fail =
  fun ({b = Int ..} -> Int) x ->
    if x\a is {b=Int ..} then x.c else 0

(* Type inference gives the correct type *)

let records3_ok =
  fun x ->
    if x\a is {b=Int ..} then x.c else 0

(* Same type as the above since the test succeeds *)

let records3bis_ok =
  fun x ->
    if x\a is {b=Int, a=?Empty ..} then x.c else 0


(* typing the addition of a field *)

let records4_ok =
  fun x ->
    if {x with a=0} is {a=Int ..} then true else false

(* typing the deletion of a field *)

let records5_ok = fun x -> x\l


(*
 Example of a switch based on the content of
 the field nodeType. Eplicit and implicit versions
 *)

type Document = { nodeType=9 ..}
and NodeList = Nil | (Node, NodeList)
and Element = { nodeType=1, childNodes = NodeList ..}
and Text = { nodeType=3, isElementContentWhiteSpace=Bool ..}
and Node = Document | Element | Text

let is_empty_node_expl = fun (x : Node) ->
  if x.nodeType is 9 then false
  else if x.nodeType is 3 then x.isElementContentWhiteSpace
  else if x.childNodes is Nil then true else false


(*
 Warning: typing the following function fails with a stack overflow on
 Chrome-based browsers, due to the very small JavaScript call stack.
 It is correctly typechecked when using Firefox or the native prototype.
*)
  
let is_empty_node_impl = fun x ->
  if x.nodeType is 9 then false
  else if x.nodeType is 3 then x.isElementContentWhiteSpace
  else if x.childNodes is Nil then true else false
