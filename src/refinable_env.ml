open Variable

type t =
  | Base of Env.t
  | Ref of t * Env.t

let from_env b = Base b

let push t = Ref (t, Env.empty)
let pop t = match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (t, _) -> t

let rec domain t =
  match t with
  | Base b -> Env.domain b
  | Ref (b, r) ->
    let d1 = domain b |> VarSet.of_list in
    let d2 = Env.domain r |> VarSet.of_list in
    VarSet.union d1 d2 |> VarSet.elements
let rec mem v t =
  match t with
  | Base b -> Env.mem v b
  | Ref (b, r) -> mem v b || Env.mem v r
let rec find v t =
  match t with
  | Base b -> Env.find v b
  | Ref (b, r) ->
    try
      let t = find v b in
      try Cduce.cap_o t (Env.find v r)
      with Not_found -> t
    with Not_found -> Env.find v r
let rec is_empty t =
  match t with
  | Base b -> Env.is_empty b
  | Ref (b, r) -> is_empty b && Env.is_empty r

let rec domain_ref t =
  match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (_, r) -> Env.domain r
let rec mem_ref v t =
  match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (_, r) -> Env.mem v r
let rec find_ref v t =
  match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (_, r) -> Env.find v r
let rec is_empty_ref t =
  match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (_, r) -> Env.is_empty r

let strengthen v t tt =
  match tt with
  | Base b -> Base (Env.strenghten v t b)
  | Ref (b, r) ->
    if mem v b && Cduce.subtype (find v b) t then Ref (b, r)
    else Ref (b, Env.strenghten v t r)
let refine_old v t tt =
  try
    let ot = find v tt in
    if (Cduce.is_empty ot |> not) && Cduce.disjoint t ot then None
    else Some (strengthen v t tt)
  with Not_found -> None
let refine v t tt =
  let ot = find v tt in
  if (Cduce.subtype Cduce.any_or_absent ot |> not) &&
      (Cduce.is_empty ot |> not) && Cduce.disjoint t ot
  then None
  else Some (strengthen v t tt)
let rm v t =
  match t with
  | Base b -> Base (Env.rm v b)
  | Ref (b, r) when mem v b |> not -> Ref (b, Env.rm v r)
  | _ -> failwith "Variable cannot be removed because it is present in a parent environment."

let rec to_env t =
  match t with
  | Base b -> b
  | Ref (b, r) ->
    List.fold_left (fun b x ->
      let t = Env.find x r in
      Env.strengthen x t b
    ) (to_env b) (Env.domain r) (* TODO: Use destruct instead *)

(* TODO *)
let leq_ref (_,r1) (_,r2) = Env.leq r1 r2
let equiv_ref env1 env2 = leq_ref env1 env2 && leq_ref env2 env1
let leq e1 e2 = Env.leq (to_env e1) (to_env e2)
let equiv env1 env2 = leq env1 env2 && leq env2 env1

let show (_,r) = Env.show r
let pp fmt (_,r) = Env.pp fmt r
let pp_filtered lst fmt (_,r) = Env.pp_filtered lst fmt r
