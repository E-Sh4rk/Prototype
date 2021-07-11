(****************************************************
  we define a fixpoint combinator that takes a 
  function of type 
     (Input -> Output) -> (Input -> Output)
  and returns its fixpoint of type
                (Input -> Output) 
  then we use it to define a diverging expression
   (set Input = Any and Output = Empty and the 
    system will deduce the type Empty for it)
  and the factorial function
 ****************************************************)

type Input = Int (* Put appropriate type here *)
and Output = Int (* Put appropriate type here *)

type X = X -> Input -> Output

let fixpoint = fun (f:((Input -> Output) -> Input -> Output )) ->
      let delta = fun ( x: X )  ->
         f ( fun  v -> ( x x v ))
       in delta delta

let id = fun ((Input -> Output) -> (Input -> Output)) x -> x

let diverge = (fixpoint id) 42

let ( * ) = <Int -> Int -> Int>            
let ( - ) = <Int -> Int -> Int>            

let factorial = fun x ->                             
  let fac =  fun (f : Int -> Int) ->
    fun x -> if x is 0 then 1 else x * (f(x-1))
  in (fixpoint fac) x
                                       
