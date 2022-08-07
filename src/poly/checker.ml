
exception Ill_typed of Position.t list * string

let rec typeof tenv env annot e =
  ignore (tenv, env, annot, e, typeof) ;
  failwith "TODO"

and typeof_a pos tenv env annot_a a =
  ignore (pos, tenv, env, annot_a, a, typeof_a) ;
  failwith "TODO"
