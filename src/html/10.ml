(*******************************************
  TypeScript 4.4beta adds ControlFlow to
  type the following  function f. Our system
  deduces for the function the type
  (Bool -> Bool) &
  (String -> String ) &
  (Int -> Int)
 ********************************************)

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

                   
(* explicitly-typed version of the function *)                   

let typescript_beta_f =  fun (x : String | Int | Bool) ->
  let isString = if typeof x is "String" then true else false in
  let isNumber = if typeof x is "Number" then true else false in
  let isStringOrNumber =  or_ isString isNumber in                                         
  if isStringOrNumber is True then x else x

(* implicitly-typed version. The deduced type
   is equivalent to
    (Bool -> Bool) &
    (String -> String ) &
    (Int -> Int) &
    (¬(Bool∣String|Int) ->  ¬(Bool∣String|Int)) *)

  
let typescript_beta_f_implicit =  fun x ->
  let isString = if typeof x is "String" then true else false in
  let isNumber = if typeof x is "Number" then true else false in
  let isStringOrNumber =  or_ isString isNumber in                                         
  if isStringOrNumber is True then x else x
