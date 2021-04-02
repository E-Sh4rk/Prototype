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

(* Examples from the previous paper *)
let two_steps =
  let f = fun (( Any\Int -> (Any, Any)\(Int,Int) ) & ( Int -> (Int,Int) )) x -> magic
  in
  fun x ->
    if snd (f x) is Int
    then
      if fst (f x) is Int then x
      else 0
    else 0

let plus = <Int->Int->Int>
let bti = <Bool->Int>
let incr = <Int->Int>

let appl1_fail =
  fun ( ((Int -> Int) | (Bool -> Bool)) -> (Int | Bool) -> (Int | Bool)) x1 ->
    fun ( (Int | Bool) -> (Int | Bool) ) x2 ->
      if (x1 x2) is Int then plus x2 (x1 x2) else land x2 (x1 x2)

let appl1_ok =
  fun ( ((Int -> Int) & (Bool -> Bool)) -> (Int | Bool) -> (Int | Bool)) x1 ->
    fun ( (Int | Bool) -> (Int | Bool) ) x2 ->
      if (x1 x2) is Int then plus x2 (x1 x2) else land x2 (x1 x2)

let appl2 =
  let bti =
    fun (Bool -> Int) b -> magic
  in
  fun ( ( (Int|Char -> Int) | (Bool|Char -> Bool) ) -> Char -> Int) x1 ->
    fun (Char -> Int) x2 ->
      if (x1 x2) is Int then incr (x1 (x1 x2)) else bti (x1 (x1 x2))

(* Examples on records *)

let records_fail =
  let destruct = fun ({id=Int} -> Int) x -> x.id in
  let record = { id=0, name='a' } in
  destruct record

let records_ok =
  let destruct = fun ({id=Int ..} -> Int) x -> x.id in
  let record = {id=0, name='a'} in
  destruct record

(* Must fail because we do not know whether x has a field a *) 
let records_fail2 =
  fun ({..} -> Any) x ->
    if {x with a=0} is {a=Int ..} then x.a else 0

(* 
  This should work because x\a is of type  {b=Int ..} since 
  it is of type {b=Int a=?Empty, ..} which is a subtype of
  {b=Int ..}
*)
let records_ok1 =
  fun ({b = Int ..} -> Int) x ->
    if x\a is {b=Int ..} then x.b else x.c

(* 
   This should fail since  x\a is of type  {b=Int a=?Empty ..} 
   which is a subtype of {b=Int ..} = {b=Int a=?Any ..}  
*)
let records_fail1 =
  fun ({b = Int ..} -> Int) x ->
    if x\a is {b=Int ..} then x.c else 0


(*  This should also fail for the same reasons as above *)
let records_fail1bis =
  fun ({b = Int ..} -> Int) x ->
    if x\a is {b=Int, a=?Empty ..} then x.c else 0

let records_ok2 =
  let x = { flag=true } in
  {x with id=10}

let records_ok3 =
  let x = { flag=true, id=10 } in
  x\flag
  
let records_ok4 =
  fun x ->
    if {x with a=0} is {a=Int ..} then true else false

let w = {b = 3, c=4}\l 

(* Memento: we should improve the printing of types. When the 
   type is closed we should not print the fields of type =?Empty
 *)

let x = <{..}>
let y = {x with a = 0}         
let u = if {x with a=0} is {..} then 0 else 1
let v = if {x with a=0} is {b=?Any ..} then 0 else 1
let s = if {x with a=0} is {a=?Bool ..} then 0 else 1      
let t = if {x with a=0} is {a=Int ..} then 0 else 1      
let z = if {x with a=0} is {b=?Empty ..} then 0 else x.b

let records_ok5 =
  fun x ->
    if {x with a=0} is {a=Int, b=Bool ..} then true else false

let paper_example1 =
  fun x ->
    if {x with a=0} is {a=Int, b=Bool ..} | {a=Bool, b=Int ..} then true else false

let paper_example2 =
  fun x ->
    if x is {a=Int, b=Bool ..} | {a=Bool, b=Int ..} then true else false

let paper_example3 =
  fun x ->
    if x is {a=Int, b=Bool ..} | {a=Bool, b=Int ..} then x.b else false
  
let paper_example4 =
  fun x ->
    if {x with a=0} is {a=Int, b=Bool ..} | {a=Bool, b=Int ..} then x.b else false

let paper_example =
  fun ({..} -> Bool) x ->
    if {x with a=0} is {a=Int, b=Bool ..} | {a=Bool, b=Int ..} then x.b else false

type Document = { nodeType=9 ..}
and NodeList = Nil | (Node, NodeList)
and Element = { nodeType=1, childNodes = NodeList ..}
and Text = { nodeType=3, isElementContentWhiteSpace=Bool ..}
and Node = Document | Element | Text

let is_empty_node = fun (x : Node) ->
  if x.nodeType is 9 then false
  else if x.nodeType is 3 then x.isElementContentWhiteSpace
  else if x.childNodes is Nil then true else false

(* Examples with recursive functions *)

(*
type IntList = Nil | (Int,IntList)
 and AnyList = Nil | (Any, AnyList)                   
 and IntTree = (Any \IntList) | Nil | (IntList,IntTree)
      
let concat = fun (x : AnyList) ->
              fun (y : AnyList) ->
                  if x is Nil then y else (fst x , (concat (snd x) y)) 
                                  
let flatten = fun x ->
  if x is Nil then true
  else if x is (Any,Any) then concat (flatten(fst x)) (flatten(snd x))
  else (x,nil)
*)

(* Test with strings *)

let typeof x =
  if x is String then "String"
  else if x is Char then "Char"
  else if x is Int then "Number"
  else if x is Bool then "Boolean"
  else if x is Unit|Nil then "Nil"
  else "Object"

let test_typeof y =
  if typeof y is "Boolean" then lnot y else false

(* Test with lists *)

let hd (x:(Any, List)) = fst x
let is_empty (x:List) =
  if x is [] then true else false

let test_hd y =
  if y is List
  then if lnot (is_empty y) then hd y
  else nil else 0

let various = [0; "ML"; nil]
let various_fun (x:[Int ; String ; List]) = fst (snd x)
let various_test = various_fun various

(* Test prefix/infix operators *)

let (+) = <Int -> Int -> Int>
let (-) = <Int -> Int -> Int>
let ( * ) = <Int -> Int -> Int>
let (/) = <Int -> Int -> Int>
let (=) = <Int -> Int -> Bool>
let (!) = <Bool -> Bool> (* Operators starting with ? or ! are prefix *)

let infix_test (x:Int) (y:Bool) = land (! (((1*x) - 3) = 6)) y

(* Fix-point combinator *)

type Input = Int (* Any   *)
and Output = Int (* Empty *)

type X = X -> Input -> Output

let fixpoint = fun (((Input -> Output) -> Input -> Output ) -> (Input -> Output)) f ->
      let delta = fun ( X -> (Input -> Output) ) x ->
         f ( fun (Input -> Output) v -> ( x x v ))
       in delta delta

let id = fun ((Input -> Output) -> (Input -> Output)) x -> x

let diverge = fixpoint id

let fac1 =  fun ((Int -> Int) -> (Int -> Int)) f ->
  fun (Int -> Int) x -> if x is (0--1) then 1 else x * (f(x-1))
               
let fac2 =  fun (f : Int -> Int) ->
  fun (x : Int) -> if x is 0 then 1 else x * (f(x-1))

let fac3 =  fun (f : Int -> Int) ->
  fun x -> if x is 0 then 1 else x * (f(x-1))
let factorial = fixpoint fac3
