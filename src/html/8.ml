(**********************************************
         we simulate JavaScript™ typeof
 **********************************************)

let incr = fun (Int -> Int) x -> magic
let charcode = fun (Char -> Int) x-> magic
let int_of_bool = fun (Bool -> Int) x -> magic

let typeof = fun x ->
    if x is Int then "number"
    else if x is Char then "string"
    else if x is Bool then "boolean"
    else "object"

let test = fun x ->
    if typeof x is "number" then incr x
    else if typeof x is "string" then charcode x
    else if typeof x is "boolean" then int_of_bool x
    else 0
