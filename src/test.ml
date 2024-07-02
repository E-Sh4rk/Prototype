(* TODO: fix (issue tallying cdcue?) *)
(* debug let rec test (f,(x,ll)) =
  (f x, test (f,ll)) *)

let succ = <Int->Int>

let aliasing (x : Any -> Any) = 
  let y = x in if x y is Int then (y x) + 1 else 42

let impossible_branch = fun x ->
  if x is Int then x + 1 else (42 3)

let impossible_branch2 = fun x -> fun y ->
  if y is Int then y+1 else x+1

let switch1 f s a b =
  if s then f a else f b

let switch2 s f a b =
  if s then f a else f b

let typeof x =
  if x is Unit|Nil then "Nil"
  else if x is String then "String"
  else if x is Char then "Char"
  else if x is Int then "Number"
  else if x is Bool then "Boolean"
  else "Object"

let lnot = fun a ->
  if a is True then false else true

let lor = fun a -> fun b ->
  if a is False then if b is False then false else true else true

let land = fun a -> fun b ->
  if a is True then if b is False then false else true else false

let tautology = fun x -> fun y ->
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

let and_js = fun x -> fun y ->
  if x is Falsy then x else y

let not_js = fun x -> if x is Falsy then 1 else 0

let or_js = fun x -> fun y ->
  if x is Truthy then x else y

let identity_js = fun x -> or_js x x

let and_pair = fun x -> fun y ->
  if x is Falsy then x else (y, succ x)

let test = fun x ->
  if fst x is Falsy then (fst x) + (snd x) else succ (fst x)

(*
  version of fixpoint with simpler typing:

  let fixpoint = <(('a -> 'b) -> ('a -> 'b)) -> ('a -> 'b) > 

  version of fixpoint with the typing deduced by the system:

  let fixpoint = <(('a -> 'b) -> (('a -> 'b) & 'c)) -> (('a -> 'b) & 'c) > 
*)

let concat_stub concat x y =
   if x is Nil then y else (fst x, (concat (snd x) y))

let concat : ['a*] -> ['b*] -> ['a* ; 'b*] = fixpoint concat_stub

let flatten_ocaml flatten x =
  if x is Nil then nil else
  if x is (Any, Any) then concat (fst x) (flatten (snd x)) else
  (x,nil)

let flatten_ocaml : [['a*]*] -> ['a*] = fixpoint flatten_ocaml 

let reverse_stub reverse l  =
    if l is Nil then nil else concat (reverse (snd l)) [(fst l)]
    
let reverse = fixpoint reverse_stub

let reverse_ann : [ ('a)*] -> [('a)*] = reverse

let rev_tl_stub rev_tl l acc  =
     if l is Nil then acc else rev_tl (snd l) (fst l, acc)

let rev_tl l = (fixpoint rev_tl_stub) l nil

let foldr_stub foldr f l acc =
   if l is Nil then acc else f (fst l) (foldr f (snd l) acc)

let foldr = fixpoint foldr_stub

let foldr_ann : ('a -> 'b -> 'b ) -> [ 'a* ] -> 'b -> 'b = foldr

(* MANY VARIANTS OF FILTER *)

let filter_stub filter (f: ('a->True) & ('b -> ~True)) (l:[('a|'b)*]) =
   if l is Nil then nil else
   if l is [Any+] then
       if f(fst(l)) is True then (fst(l),filter f (snd(l))) else filter f (snd(l))
   else 42(3)

let filter = fixpoint filter_stub

let filter2_stub
  (filter : ((('a & 'b) -> Any) & (('a\'b) -> ~True)) -> [ 'a* ] -> [ ('a&'b)* ] )
  (f : (('a & 'b) -> Any) & (('a\'b) -> ~True))
  (l : [ ('a)*  ] )  =
  (* filter f l = *)
  if l is Nil then nil
  else
    if f(fst(l)) is True then (fst(l),filter f (snd(l))) else filter f (snd(l))

let filter2 :  ((('a & 'b) -> Any) & (('a\'b) -> ~True)) -> [ 'a* ] -> [ ('a&'b)* ] =
      fixpoint filter2_stub

let x = <Int -> Bool>

let filter2_partial_app = filter2 x

(*
    Here a better version with head and tail:
    it yields exactly the same type as the version above
*)

let filter3_stub
  (filter : ((('a & 'b) -> True) & (('a\'b) -> ~True)) -> [ 'a* ] -> [ ('a&'b)* ] )
  (f : (('a & 'b) -> True) & (('a\'b) -> ~True))
  (l : [ ('a)*  ] )  =
   if l is Nil then nil else
       let h = fst(l) in
       let t = snd(l) in
       if f h is True then (h ,filter f t) else filter f t

let filter3 :  ((('a & 'b) -> True) & (('a\'b) -> ~True)) -> [ 'a* ] -> [ ('a&'b)* ] =
      fixpoint filter3_stub

let filter4_stub
  (filter : ((('a) -> True) & (('b) -> ~True)) -> [ ('a|'b)* ] -> [ ('a)* ] )
  (f : (('a) -> True) & (('b) -> ~True))
  (l : [ ('a|'b)* ] )  =
   if l is Nil then nil else
       let h = fst(l) in
       let t = snd(l) in
       if f h is True then (h ,filter f t) else filter f t

let filter4 : ((('a) -> True) & (('b) -> ~True)) -> [ ('a|'b)* ] -> [ ('a)* ] =
      fixpoint filter4_stub

let xi = <(Int -> True) & (Bool -> False)>

let filter3_test = filter3 xi [1;3;true;42]

let filter4_test = filter4 xi (1, (3, (true,(42,nil))))

(* cross typing on the two versions *)

let filter4_as_3 : ((('a & 'b) -> True) & (('a\'b) -> ~True)) -> [ 'a* ] -> [ ('a&'b)* ] =
      fixpoint filter4_stub

let filter3_as_4 : ((('a) -> True) & (('b) -> ~True)) -> [ ('a|'b)* ] -> [ ('a)* ]  =
      fixpoint filter3_stub

let filter_classic_stub
  (filter : (('a) -> Bool) -> [ ('a)* ] -> [ ('a)* ] ) ( f : 'a -> Bool) (l : [ ('a)* ] ) =
  (* filter f l = *)
  if l is Nil then nil
  else
    if f(fst(l)) is True then (fst(l),filter f (snd(l))) else filter f (snd(l))

let filter_classic = fixpoint filter_classic_stub

(* A version where the predicate function must cover Any *)

let filter_total_stub
  (filter : (('a -> True) & ((~('a)) -> ~True)) -> [ Any* ] -> [ ('a)* ] )
  ( f : (('a -> True) & ((~('a)) -> ~True))) (l : [ Any* ] )  =
   if l is Nil then nil else
   if f(fst(l)) is True then (fst(l),filter f (snd(l))) else filter f (snd(l))

let filter_total : (('a -> True) & ((~'a) -> ~True)) -> [Any*] -> [ ('a)* ] = fixpoint filter_total_stub

(* DEEP FLATTEN FUNCTION *)

let flatten_noannot_stub flatten x =
  if x is Nil then nil else
  if x is [Any*] then concat (flatten (fst x)) (flatten (snd x))
  else (x,nil)

(* let flatten_noannot = fixpoint flatten_noannot_stub *)

type Tree 'a = ('a \ [Any*]) | [(Tree 'a)*]

let flatten_stub flatten (x : Tree 'a) =
  if x is Nil then nil else
  if x is [Any*] then concat (flatten (fst x)) (flatten (snd x))
  else (x,nil)

let flatten = fixpoint flatten_stub

let flatten_ann : (Tree 'a -> ['a*]) = flatten 

let test_flatten = flatten ((1,(true,nil)),(((42,(false,nil)),0),"ok"))

(* MISCELLANEOUS *)

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

let test3_patterns_ann x y =
  let pack (x:'a;'b) (y:'a;'b) = (x,y) in
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

let fact_pat_stub fact n =
  match n with
  | :0 -> 1
  | n -> (fact (n-1))*n
  end

let fact_pat = fixpoint fact_pat_stub

let length_pat_stub length lst =
  match lst with
  | [] -> 0
  | (_, tl & :List) -> succ (length tl)
  end

let length_pat = fixpoint length_pat_stub

let map_pat_stub map f lst =
  match lst with
  | [] -> []
  | (hd, tl) & :List -> (f hd, map f tl)
  end

let map_pat = fixpoint map_pat_stub

(* Recursive functions and partial user type annotations *)

let rec map_noannot f lst =
  match lst with
  | [] -> []
  | (e,lst) & :List -> ((f e), map_noannot f lst)
  end

let rec map f (lst:['a*]) =
  match lst with
  | [] -> []
  | (e,lst) & :List -> ((f e), map f lst)
  end

(* let rec filter_noannot f l =
  if l is Nil then nil
  else
    if f(fst(l)) is True
    then (fst(l),filter f (snd(l)))
    else filter f (snd(l)) *)

let rec filter (f: ('a->Any) & ('b -> ~True)) (l:[('a|'b)*]) =
  match l with
  | :Nil -> nil
  | (e,l) ->
    if f e is True
    then (e, filter f l)
    else filter f l
  end
    
(* let rec flatten_noannot x =
  if x is Nil then nil else
  if x is [Any*] then concat (flatten (fst x)) (flatten (snd x))
  else (x,nil) *)

let rec flatten (x : Tree('a)) =    
  if x is Nil then nil else
  if x is [Any*] then concat (flatten (fst x)) (flatten (snd x))
  else (x,nil)

let rec mapi_aux i f l =
  match l with
  :Nil -> []
  | (x, ll) -> let r = f i x in (r, mapi_aux (i+1) f ll)
end

let mapi f l = mapi_aux 0 f l
  
let rec eval e =
  match e with
  | (:"add", (e1, e2)) -> (eval e1) + (eval e2)
  | (:"uminus", e) -> 0 - (eval e)
  | (:"const", x) -> x
  end

type Expr = ("const", (0--)) | ("add", (Expr, Expr)) | ("uminus", Expr)

let rec eval_ann (e:Expr) =
  match e with
  | (:"add", (e1, e2)) -> (eval_ann e1) + (eval_ann e2)
  | (:"uminus", e) -> 0 - (eval_ann e)
  | (:"const", x) -> x
  end

(* ===== EXAMPLES FROM THE PAPER ===== *)

let toBoolean x =
    if x is Truthy then true else false

let lOr (x,y) =
    if toBoolean x then x else y

let id x =
    lOr (x,x)

let fixpoint = fun f ->
  let delta = fun x ->
      f ( fun  v -> ( x x v ))
  in delta delta

let map_stub map f lst =
  if lst is Nil then nil
  else (f (fst lst), map f (snd lst))

let map = fixpoint map_stub

let filter_stub filter (f: ('a->Any) & ('b -> ~True)) (l:[('a|'b)*]) =
  if l is Nil then nil
  else if f(fst(l)) is True
  then (fst(l), filter f (snd(l)))
  else filter f (snd(l))

let filter = fixpoint filter_stub

let rec (concat : ['a*] -> ['b*] -> ['a* ; 'b*]) x y =
  match x with
  | [] -> y
  | (h, t) -> (h, concat t y)
  end

let rec flatten x = match x with
 | [] -> []
 | (h, t) & :List -> concat (flatten h) (flatten t)
 | _ -> [x]
end

let rec filter f (l:['a*]) =
  match l with
  | [] -> []
  | (h,t) & :List -> if f h
             then (h, filter f t)
             else filter f t
  end

let rec fold_right f acc l =
  match l with
  :Nil -> acc
  | (x, ll) -> f x (fold_right f acc ll)
end

(* UNCOMPLETENESS & ANNOTATIONS *)

let id x = x

let test_expansion_noannot =
    let f = (fun x -> (x 123, x true)) in
    f id

let test_expansion =
  let f = (fun x -> (x 123, x true)) in
  f (id :> (123 -> 123) ; (True -> True))

let f = < ('a -> 'a) -> ('a -> 'a) >
let x = < (Int -> Int) | (Bool -> Bool) >

let test_expansion2_noannot = f x

let test_expansion2 =
  (f :> ((Int -> Int) -> (Int -> Int)) ;
        ((Bool -> Bool) -> (Bool -> Bool))) x

let bool = <Unit -> Bool>
let neg = <(True -> False) & (False -> True)>
let lor = <(True -> Bool -> True)
  & (Bool -> True -> True) & (False -> False -> False)>

let test_split_noannot =
  let b = bool () in
  lor (neg b) b

let test_split =
  let b = (bool () : True ; False) in
  lor (neg b) b

(* Cons syntax *)

let hd2 x =
  match x with
  | _::b::_ -> b
  end

let cons2 x y z = x::y::z

let test_cons = hd2 (cons2 'a' 'b' ['c';'d'])

let rec first_leaf (x : T | Unit where T = [T+] | Int) =
  match x with
  | () -> nil
  | b::_ -> first_leaf b
  | i -> i
  end
