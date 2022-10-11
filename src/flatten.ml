let fixpoint = fun f ->
  let delta = fun x ->
     f ( fun  v -> ( x x v ))
   in delta delta


let concat_pre concat x y =
   if x is Nil then y else (fst x, (concat (snd x) y))

let concat = fixpoint concat_pre
let concat_check : [ 'a* ] -> [ 'b* ] -> [ 'a* ; 'b* ] = fixpoint concat_pre

type Tree 'a = ('a \ [Any*]) | [(Tree 'a)*]

(* Without this annotation, flatten_pure type is correct
   but huge with multiple copies of the same recursive types.
   The type of fixpoint flatten is then too large (but correct).

With such a huge type, flatten_pure_check is typechecked with a large type,
flattench_check typechecks in 11seconds (so the large type is indeed
correct) and flatten pure cannot type check in several minutes with 16GB Ram.

let concat = < [ 'a* ] -> [ 'b* ] -> [ 'a* ; 'b* ] >
*)


(* Without this annotation on x, the type inferred for flatten_pure
   is incorrect, need to investigate (tallying returns wrong substitutions *)

let flatten_pure flatten (x : Tree('a)) =
  if x is Nil then nil else
  if x is [Any*] then concat (flatten (fst x)) (flatten (snd x))
  else (x,nil)


let flatten_pure_check : (Tree ('a) -> [('a\[Any*])*]) -> Tree ('a) -> [('a\[Any*])*] = flatten_pure

let flatten = fixpoint flatten_pure

let flatten_check : Tree ('a) -> [('a\[Any*])*] = fixpoint flatten_pure
