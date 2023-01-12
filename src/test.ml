
let (-) = <Int->Int->Int>
let (+) = <Int->Int->Int>
let ( * ) = <Int->Int->Int>
let succ = <Int->Int>

let more_than_declarative (x : Any -> Any) = 
    let y = x in if x y is Int then (y x) + 1 else 42

let impossible_branch = fun x ->
    if x is Int then x + 1 else (42 3)

let impossible_branch2 = fun x -> fun y ->
  if y is Int then y+1 else x+1

let switch1 f s a b =
    if s then f a else f b

let switch2 s f a b =
    if s then f a else f b

(* ======================================= *)

let typeof x =
  if x is Unit|Nil then "Nil"
  else if x is String then "String"
  else if x is Char then "Char"
  else if x is Int then "Number"
  else if x is Bool then "Boolean"
  else "Object"

(* ======================================= *)

let lnot = fun a ->
  if a is True then false else true

let lor = fun a -> fun b ->
  if a is False then if b is False then false else true else true

let land = fun a -> fun b ->
  if a is True then if b is False then false else true else false

let test_1 = fun x -> fun y ->
  if land (lor x (lnot x)) (lor (lnot y) y) then true else false

(* ============== RECURSIVE ============= *)

(* The type deduced for fixpoint can be read as follows
   forall('c <: 'a -> 'b)('d <:'c). ('c -> 'd) -> 'd 
*)
let fixpoint = fun f ->
  let delta = fun x ->
     f ( fun  v -> ( x x v ))
   in delta delta


let fact fact n =
  if n is 0 then 1 else (fact (n-1))*n

let fact = fixpoint fact

let length length lst =
  if lst is Nil then 0 else succ (length (snd lst))

let length = fixpoint length

let map map f lst =
  if lst is Nil then nil
  else (f (fst lst), map f (snd lst))

let map = fixpoint map

(*************************************************
*          Tobin-Hochstadt & Felleisen           *
*     exampleX = EXPLICITLY ANNOTATED VERSIONS   *
*     implictX = IMPLICITLY ANNOTATED VERSIONS   *
*                                                *
**************************************************)

(*
 Interesting points:
  - example2: does not need the annotation, while TH&F yes
  - example6: not typable with the annotation Int|String
    (as expected), but if we remove annotations becomes typable.
    That is our system finds the right constraints to make the
    expression typable
  - in examples 10 11 12 we do not have to assume that p is
    a product the system deduces it alone
  - same for the example 14. We do not have to assume that
    the parameter input is Int|String and extra is a pair. The system
    finds it alone and it works for user defined "and"
    (currified or not)
*)

(* prelude *)

atom no

let and_ = fun x -> fun y ->
     if x is True then if y is True then y else false else false
let fst2 = <('a, Any) -> 'a>
let snd2 = <(Any, 'a) -> 'a>
let and2_ = fun x ->
  if fst2 x is True then if snd2 x is True then fst2 x else false else false
let and2_ = fun x ->
     if fst x is True then if snd x is True then fst x else false else false

let not_ = fun x -> if x is True then false else true

let or_ =  fun x -> fun y -> not_ (and_ (not_ x) (not_ y))

let is_string = fun x ->
     if x is String then true else false

let is_int = fun x ->
     if x is Int then true else false

let strlen = <(String) -> Int>

let add = <Int -> Int -> Int>

let add1 = <Int -> Int>

let f = <(Int | String) -> Int>

let g = <(Int, Int) -> Int>


(* Examples Tobin-Hochstadt & Felleisen *)

let example1 = fun (x:Any) ->
  if x is Int then add1 x else 0

let implict1 = fun x ->
  if x is Int then add1 x else 0


let example2 = fun (x:String|Int) ->
  if x is Int then add1 x else strlen x

let implict2 = fun x ->
  if x is Int then add1 x else strlen x


let example3 = fun (x: Any) ->
  if x is (Any \ False) then (x,x) else false

let implict3 = fun x ->
  if x is (Any \ False) then (x,x) else false


let example4 = fun (x : Any) ->
  if or_ (is_int x) (is_string x) is True then x else 'A'

let implict4 = fun x ->
  if or_ (is_int x) (is_string x) is True then x else 'A'


let example5 = fun (x : Any) -> fun (y : Any) ->
  if and_ (is_int x) (is_string y) is True then
   add x (strlen y) else 0

let implict5 = fun x -> fun y ->
  if and_ (is_int x) (is_string y) is True then
   add x (strlen y) else 0


let example6 = fun (x : Int|String) -> fun (y : Any) ->
  if and_ (is_int x) (is_string y) is True then
   add  x (strlen y) else strlen x

let implict6 = fun x -> fun y ->
  if and_ (is_int x) (is_string y) is True then
   add  x (strlen y) else strlen x


let example7 = fun (x : Any) -> fun (y : Any) ->
  if  (if (is_int x) is True then (is_string y) else false) is True then
   add x (strlen y) else 0

let implict7 = fun x -> fun y ->
  if  (if (is_int x) is True then (is_string y) else false) is True then
   add x (strlen y) else 0


let example8 = fun (x : Any) ->
  if or_ (is_int x) (is_string x) is True then true else false

let implict8 = fun x ->
  if or_ (is_int x) (is_string x) is True then true else false


let example9 = fun (x : Any) ->
  if
   (if is_int x is True then is_int x else is_string x)
   is True then  f x else 0

let implict9 = fun x  ->
  if
   (if is_int x is True then is_int x else is_string x)
   is True then  f x else 0


let example10 = fun (p : (Any,Any)) ->
  if is_int (fst p) is True then add1 (fst p) else 7

let implict10 = fun p ->
  if is_int (fst p) is True then add1 (fst p) else 7


let example11 = fun (p : (Any, Any)) ->
  if and_ (is_int (fst p)) (is_int (snd p)) is True then g p else no

let implict11 = fun p ->
  if and_ (is_int (fst p)) (is_int (snd p)) is True then g p else no


let example12 = fun (p : (Any, Any)) ->
  if is_int (fst p) is True then true else false

let implict12 = fun p ->
  if is_int (fst p) is True then true else false


let example13 =
 fun (x : Any) ->
   fun (y : Any) ->
    if and_ (is_int x) (is_string y) is True then 1
    else if is_int x is True then 2
    else 3

let implict13 =
 fun x ->
   fun y ->
    if and_ (is_int x) (is_string y) is True then 1
    else if is_int x is True then 2
    else 3


(* uncurried "and" *)
let example14 = fun (input : Int|String) ->
fun (extra : (Any, Any)) ->
 if and2_(is_int input , is_int(fst extra)) is True then
     add input (fst extra)
 else if is_int(fst extra) is True then
     add (strlen input) (fst extra)
 else 0

let implct14a = fun (input : Int|String) ->
fun extra ->
 if and2_(is_int input , is_int(fst extra)) is True then
     add input (fst extra)
 else if is_int(fst extra) is True then
     add (strlen input) (fst extra)
 else 0

let implct14b = fun input ->
fun extra ->
 if and2_(is_int input , is_int(fst extra)) is True then
     add input (fst extra)
 else if is_int(fst extra) is True then
     add (strlen input) (fst extra)
 else 0

(* curried "and" *)
let curried14 = fun (input : Int|String) ->
fun (extra : (Any, Any)) ->
 if and_ (is_int input) (is_int(fst extra)) is True then
     add input (fst extra)
 else if is_int (fst extra) is True then
     add (strlen input) (fst extra)
 else 0

let currid14a = fun (input : Int|String) ->
fun extra ->
 if and_ (is_int input) (is_int(fst extra)) is True then
     add input (fst extra)
 else if is_int (fst extra) is True then
     add (strlen input) (fst extra)
 else 0

let currid14b = fun input ->
fun extra ->
 if and_ (is_int input) (is_int(fst extra)) is True then
     add input (fst extra)
 else if is_int (fst extra) is True then
     add (strlen input) (fst extra)
else 0


     
(*******************************
 *                             *
 *  Examples for polymorphism  *
 *                             *
 *******************************)

type Falsy = False | "" | 0
type Truthy = ~Falsy

let succ = <Int -> Int>

let and_js = fun x -> fun y ->
  if x is Falsy then x else y

(* expected type:    
      ('a & Falsy -> Any -> 'a & Falsy)
     &(Truthy -> 'b -> 'b)
*)


let not_js = fun x -> if x is Falsy then 1 else 0

let or_js = fun x -> fun y ->
   if x is Truthy then x else y

let identity_js = fun x -> or_js x x

let and_and = fun x -> fun y ->
  if x is Falsy then x else (y, succ x)

(* expected type:
      ('a & Falsy -> Any -> 'a & Falsy)
     &(Truthy&(Int\0) -> 'b -> ('b,Int))
*)

 let test = fun x ->
   if fst x is Falsy then (fst x) + (snd x) else succ (fst x)

(* expected type
    (0,Int) | (Int\0,Any) -> Int
*)

(*
  version of fixpoint with simpler typing:

  let fixpoint = <(('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b) > 

  version of fixpoint with the typing deduced by the system:

  let fixpoint = <(('a -> 'b) -> (('a -> 'b) & 'c)) -> (('a -> 'b) & 'c) > 
*)

let concat_stub concat x y =
   if x is Nil then y else (fst x, (concat (snd x) y))

let concat = fixpoint concat_stub

let concat : ['a*] -> ['b*] -> ['a* ; 'b*] = fixpoint concat_stub

let flatten_ocaml flatten (x:['_a*]) =
  if x is Nil then nil else
  if x is (Any, Any) then concat (fst x) (flatten (snd x)) else
  (x,nil)

let flatten_ocaml : [['a*]*] -> ['a*] = fixpoint flatten_ocaml 

let reverse_aux reverse l  =
    if l is Nil then nil else concat (reverse (snd l)) [(fst l)]
    
let reverse  = fixpoint reverse_aux

let reverse_ann : [ ('a)*] -> [('a)*] = fixpoint reverse_aux

let rev_tl_aux rev_tl l acc  =
     if l is Nil then acc else rev_tl (snd l) (fst l, acc)

(* two different typings for fixpoint:
let fixpoint = <(('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b) >
let fixpoint = <(('a -> 'b) -> (('a -> 'b) & 'c)) -> (('a -> 'b) & 'c) >
*)
let fixpoint = <(('a -> 'b) -> (('a -> 'b) & 'c)) -> (('a -> 'b) & 'c) >

let rev_tl l = (fixpoint rev_tl_aux) l nil

let foldr_aux foldr f l acc =
   if l is Nil then acc else f (fst l) (foldr f (snd l) acc)

let foldr = fixpoint foldr_aux

let foldr_ann : ('a -> 'b -> 'b ) -> [ 'a* ] -> 'b -> 'b = fixpoint foldr_aux

let foldr_ann2 : (('a -> 'b -> 'b ) -> [ 'a* ] -> 'b -> 'b) & (Any -> [] -> 'c -> 'c)  =
    fixpoint foldr_aux 

(* FILTER FUNCTION *)

let filter_aux_pure filter (f: ('a->True) & ('b -> ~True)) (l:[('a|'b)*]) =
   if l is Nil then nil else
   if l is [Any+] then
       if f(fst(l)) is True then (fst(l),filter f (snd(l))) else filter f (snd(l))
   else 42(3)

let filter = fixpoint filter_aux_pure

let filter_aux_pure_noannot filter f l =
  if l is Nil then nil else
  if l is [Any+] then
      if f(fst(l)) is True then (fst(l),filter f (snd(l))) else filter f (snd(l))
  else 42(3)

(*
   A new variation that does not require the
   characteristic function to be defined on Any
 *)

let new_filter1_aux
  (filter : ((('a & 'b) -> True) & (('a\'b) -> ~True)) -> [ 'a* ] -> [ ('a&'b)* ] )
  (f : (('a & 'b) -> True) & (('a\'b) -> ~True))
  (l : [ ('a)*  ] )  =
  (* filter f l = *)
  if l is Nil then nil
  else
    if f(fst(l)) is True then (fst(l),filter f (snd(l))) else filter f (snd(l))

let new_filter :  ((('a & 'b) -> True) & (('a\'b) -> ~True)) -> [ 'a* ] -> [ ('a&'b)* ] =
      fixpoint new_filter1_aux

(* here a better version with head and tail: it yields exactly the
   same type as the version above but 10% slower
 *)

let new_filter_aux
  (filter : ((('a & 'b) -> True) & (('a\'b) -> ~True)) -> [ 'a* ] -> [ ('a&'b)* ] )
  (f : (('a & 'b) -> True) & (('a\'b) -> ~True))
  (l : [ ('a)*  ] )  =
   if l is Nil then nil else
       let h = fst(l) in
       let t = snd(l) in
       if f h is True then (h ,filter f t) else filter f t

let new_filter :  ((('a & 'b) -> True) & (('a\'b) -> ~True)) -> [ 'a* ] -> [ ('a&'b)* ] =
      fixpoint new_filter_aux

(* Notice that with the following version the result of the application is much less precise
   despite the cross typing of both works
 *)

let new_filter_2_aux
  (filter : ((('a) -> True) & (('b) -> ~True)) -> [ ('a|'b)* ] -> [ ('a)* ] )
  (f : (('a) -> True) & (('b) -> ~True))
  (l : [ ('a|'b)* ] )  =
   if l is Nil then nil else
       let h = fst(l) in
       let t = snd(l) in
       if f h is True then (h ,filter f t) else filter f t

let new_filter_2 : ((('a) -> True) & (('b) -> ~True)) -> [ ('a|'b)* ] -> [ ('a)* ]  = fixpoint new_filter_2_aux


let xi = <(Int -> True) & (Bool -> False)>

let filter_test = new_filter xi [1;3;true;42]

let filter_2_test = new_filter_2 xi (1, (3, (true,(42,nil))))

(* cross typing on the two versions *)

let new_filter_2_as_1 :  ((('a & 'b) -> True) & (('a\'b) -> ~True)) -> [ 'a* ] -> [ ('a&'b)* ] =
      fixpoint new_filter_2_aux

let new_filter_1_as_2 : ((('a) -> True) & (('b) -> ~True)) -> [ ('a|'b)* ] -> [ ('a)* ]  =
      fixpoint new_filter_aux

let filter_aux_classic
(filter : (('a) -> Bool) -> [ ('a)* ] -> [ ('a)* ] ) ( f : 'a -> Bool) (l : [ ('a)* ] )  =
  (* filter f l = *)
  if l is Nil then nil
  else
    if f(fst(l)) is True then (fst(l),filter f (snd(l))) else filter f (snd(l))


let filter_classic = fixpoint filter_aux_classic

(* Tail recursive version *)

(* The following make the type-checker diverge 
 let filter : ((('a & 'b) -> True) & (('a\'b) -> ~True)) -> [ 'a* ] -> [ ('a&'b)* ]  =
   fun f -> fun l ->
   let filter_tr_aux  
     (filter : (((('a & 'b) -> True) & (('a\'b) -> ~True)), [ 'a* ] , ['a*] ) -> [ ('a&'b)* ] )
     (args : (((('a & 'b) -> True) & (('a\'b) -> ~True)), [ ('a)* ], [ ('a)* ]) )  =
      let f = fst args in
      let l = fst (snd args) in
      let acc = snd (snd args) in
      if l is Nil then acc else
         let h = fst(l) in
         let t = snd(l) in
         if f h is True then filter (f, t , (h,acc)) else filter (f , t , acc)
   in (fixpoint filter_tr_aux) (f , l , []) 
*)

(* This type checks but it requires the domain of the function to be Any *)

let filter_aux (filter : (('a -> True) & ((~('a)) -> ~True)) -> [ Any* ] -> [ ('a)* ] ) ( f : (('a -> True) & ((~('a)) -> ~True))) (l : [ Any* ] )  =
   if l is Nil then nil else
   if f(fst(l)) is True then (fst(l),filter f (snd(l))) else filter f (snd(l))


let filter : (('a -> True) & ((~'a) -> ~True)) -> [Any*] -> [ ('a)* ] = fixpoint filter_aux


(* DEEP FLATTEN FUNCTION *)

let flatten_pure flatten x =
  if x is Nil then nil else
  if x is [Any*] then concat (flatten (fst x)) (flatten (snd x))
  else (x,nil)



(* let flatten_pure = fixpoint flatten_pure *)

type Tree 'a = ('a \ [Any*]) | [(Tree 'a)*]

let flatten_stub (flatten : Tree 'a -> ['a*]) (x : Tree 'a) =
  if x is Nil then nil else
  if x is [Any*] then concat (flatten (fst x)) (flatten (snd x))
  else (x,nil)

(* let flatten = < (Tree 'a -> ['a*]) -> (Tree 'a -> ['a*]) > *)

let flatten = fixpoint flatten_stub

let flatten_ann : (Tree 'a -> ['a*]) = fixpoint flatten_stub 


let test = flatten ((1,(true,nil)),(((42,(false,nil)),0),"ok"))

type TRUE 'a 'b  =  'a -> 'b -> 'a
type FALSE 'a 'b  =  'a -> 'b -> 'b

let ifthenelse (b : TRUE 'a 'b; FALSE 'a 'b )  x y = b x y

let check :    (TRUE 'c 'd -> 'c -> 'd -> 'c) & (FALSE 'c 'd -> 'c -> 'd -> 'd) = ifthenelse


(* Parametric types examples *)

type Tree' 'a = ('a, [(Tree' 'a)*])
let a = <Tree' Int>

type Rec 'a = Rec 'a -> 'a
let b = <Rec 'b>

(* Pattern matching *)

let test_patterns (a,_) = a

let test2_patterns x =
  match x with (a,_)&(_,b) -> (a,b) end

let test3_patterns x y =
  let pack x y = (x,y) in
  let (y,x) = pack x y in
  pack x y

let typeof_patterns x =
  match x with
  | :Unit | :Nil -> "Nil"
  | :String -> "String"
  | :Char -> "Char"
  | :Int -> "Number"
  | :Bool -> "Boolean"
  | :Any -> "Object"
  end

let land_patterns a b =
  match a,b with
  | :True, :True -> true
  | :Any -> false
  end

let fact_pat fact n =
  match n with
  | :0 -> 1
  | n -> (fact (n-1))*n
  end

let fact = fixpoint fact_pat

let length_pat length lst =
  match lst with
  | :[] -> 0
  | (_, tl & :List) -> succ (length tl)
  end

let length = fixpoint length_pat

let map_pat map f lst =
  match lst with
  | :[] -> []
  | (hd, tl) & :List -> (f hd, map f tl)
  end

let map = fixpoint map_pat
