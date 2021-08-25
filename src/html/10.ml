(**********************************************************

  TypeScript 4.4beta adds ControlFlow analysis 
  to type the functions "area" and "f" below.
  The examples come from
  https://devblogs.microsoft.com/typescript/ \
  announcing-typescript-4-4-beta/#cfa-aliased-conditions

 **********************************************************)


(* auxiliary definitions *)

let typeof x =
  if x is String then "String"
  else if x is Char then "Char"
  else if x is Int then "Number"
  else if x is Bool then "Boolean"
  else if x is Unit|Nil then "Nil"
  else "Object"

let or_ = fun a -> fun b ->
   if a is False then if b is False then false else true else true

let ( ** ) = <Int -> Int -> Int>   

                              
(* 
   explicitly typed version of the area function 
   the deduced type is Shape -> Int 
*)
                              
type Shape =
      { kind = "circle", radius = Int }
    | { kind = "square", sideLength = Int }

let area = fun (shape: Shape) ->
    let isCircle = if shape.kind is "circle" then true else false in
    if isCircle is True then
      (* We know we have a circle here! *)
        (shape.radius) ** 7 
    else 
      (* We know we're left with a square here! *)
        (shape.sideLength) ** 2


(* 
   implicitly typed version of area. The type deduced
   by our system is equivalent to    
     { kind="circle"  radius=Int .. } 
   | { kind=(¬"circle") sideLength=Int  .. }  -> Int    
*)
    
let area_implicit = fun shape ->
    let isCircle = if shape.kind is "circle" then true else false in
    if isCircle is True then
      (* We know we have a circle here! *)
        (shape.radius) ** 7 
    else 
      (* We know we're left with a square here! *)
        (shape.sideLength) ** 2

    
(* 
  explicitly-typed version of the function f 
  The type deduced for the function is:
  (Bool -> Bool) &
  (String -> String ) &
  (Int -> Int)
*)                   

let typescript_beta_f =  fun (x : String | Int | Bool) ->
  let isString = if typeof x is "String" then true else false in
  let isNumber = if typeof x is "Number" then true else false in
  let isStringOrNumber =  or_ isString isNumber in                                         
  if isStringOrNumber is True then x else x


(* implicitly-typed version for f. The deduced type
   is equivalent to
    (Bool -> Bool) &
    (String -> String ) &
    (Int -> Int) &
    (Unit -> Unit ) &
    (¬(Bool∣String|Int|Unit) ->  ¬(Bool∣String|Int|Unit)) 
*)

  
let typescript_beta_f_implicit =  fun x ->
  let isString = if typeof x is "String" then true else false in
  let isNumber = if typeof x is "Number" then true else false in
  let isStringOrNumber =  or_ isString isNumber in                                         
  if isStringOrNumber is True
    then x
    else x
