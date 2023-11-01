
let typeof x =
  match x with
  | :Nil -> "Nil"
  | :String -> "String"
  | :Char -> "Char"
  | :Int -> "Number"
  | :Bool -> "Boolean"
  | :Any -> "Object"
  end

type Expr = ("const", Int) | ("add", (Expr, Expr)) | ("uminus", Expr)

let rec eval e =
  match e with
  | (:"add", (e1, e2)) -> (eval e1) + (eval e2)
  | (:"uminus", e) -> 0 - (eval e)
  | (:"const", x) -> x
  end

let rec eval_ann (e:Expr) =
  match e with
  | (:"add", (e1, e2)) -> (eval_ann e1) + (eval_ann e2)
  | (:"uminus", e) -> 0 - (eval_ann e)
  | (:"const", x) -> x
  end

let rec map f lst =
  match lst with
  | :[] -> []
  | (e,lst) & :List -> ((f e), map f lst)
  end  

let rec map_ann f (lst:['a*]) =
  match lst with
  | :[] -> []
  | (e,lst) -> ((f e), map_ann f lst)
  end

let rec filter f (l:['a*]) =
  match l with
  | :Nil -> nil
  | (e,l) ->
      if f e is True
      then (e, filter f l)
      else filter f l
  end

let rec filter_ann (f: ('a->Any) & ('b -> ~True)) (l:[('a|'b)*]) =
  match l with
  | :Nil -> nil
  | (e,l) ->
      if f e is True
      then (e, filter_ann f l)
      else filter_ann f l
  end

let not_nil x = if x is Nil then false else true

let filtered_list = filter_ann not_nil [1;3;nil;42]

let rec concat x y =
  match x with
  | :[] -> y
  | (h, t) -> (h, concat t y)
  end
let concat : ['a*] -> ['b*] -> ['a* ; 'b*] = concat

let rec concat_ann (x:['a*]) (y:['b*]) =
  match x with
  | :[] -> y
  | (h, t) -> (h, concat_ann t y)
  end

type Tree 'a = ('a \ List) | [(Tree 'a)*]

let rec flatten x =
    match x with
    | :[] -> []
    | (h, t) & :List -> concat (flatten h) (flatten t)
    | _ -> [x]
    end
let flatten : Tree 'a -> ['a*] = flatten

let rec flatten_ann (x: Tree 'a) =
  match x with
  | :[] -> []
  | (h, t) & :List -> concat (flatten_ann h) (flatten_ann t)
  | _ -> [x]
  end

let flatten_test = flatten [[1;[2];3];4;[5;6;[];[7]]]    

(* BAL *)

let (>=) = <Int -> Int -> Bool>
let (>) = <Int -> Int -> Bool>
let invalid_arg = <String -> Empty>

atom key

type T 'a =
  Nil | (T 'a, Key, 'a, T 'a, Int)

let height x =
  match x with
  | :Nil -> 0
  | (_,_,_,_,h) -> h
  end

let create l x d r =
  let hl = height l in
  let hr = height r in
  (l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

let bal (l:T 'a) (x: Key) (d:'a) (r:T 'a) =
  let hl = match l with :Nil -> 0 | (_,_,_,_,h) -> h end in
  let hr = match r with :Nil -> 0 | (_,_,_,_,h) -> h end in
  if hl > (hr + 2) then
    match l with
    | :Nil -> invalid_arg "Map.bal"
    | (ll, lv, ld, lr, _) ->
      if (height ll) >= (height lr) then
        create ll lv ld (create lr x d r)
      else
        match lr with
        | :Nil -> invalid_arg "Map.bal"
        | (lrl, lrv, lrd, lrr, _)->
          create (create ll lv ld lrl) lrv lrd (create lrr x d r)
        end
    end
  else if hr > (hl + 2) then
    match r with
    | :Nil -> invalid_arg "Map.bal"
    | (rl, rv, rd, rr, _) ->
      if (height rr) >= (height rl) then
        create (create l x d rl) rv rd rr
      else
        match rl with
        | :Nil -> invalid_arg "Map.bal"
        | (rll, rlv, rld, rlr, _) ->
          create (create l x d rll) rlv rld (create rlr rv rd rr)
        end
    end
  else (l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

let bal : T 'a -> Key -> 'a -> T 'a -> T 'a = bal
