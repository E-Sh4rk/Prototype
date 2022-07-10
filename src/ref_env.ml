open Variable

type t =
  | Base of Env.t
  | Ref of t * Env.t

let from_env b = Base b
let rec to_env t =
  match t with
  | Base b -> b
  | Ref (b, r) ->
    List.fold_left (fun b (x,t) ->
      Env.strengthen x t b
    ) (to_env b) (Env.bindings r)

let push t = Ref (t, Env.empty)
let merge t = match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (b, r) ->
    let env = match b with Base b -> b | Ref (_, r) -> r in
    let env = List.fold_left (fun e (x,t) ->
        Env.strengthen x t e
      ) env (Env.bindings r)
    in
    match b with Base _ -> Base env | Ref (b, _) -> Ref (b, env)
let pop t = match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (b, _) -> b

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
let bindings t = to_env t |> Env.bindings

let domain_ref t =
  match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (_, r) -> Env.domain r
let mem_ref v t =
  match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (_, r) -> Env.mem v r
let find_ref v t =
  match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (_, r) -> Env.find v r
let is_empty_ref t =
  match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (_, r) -> Env.is_empty r
let bindings_ref t =
  match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (_, r) -> Env.bindings r

let strengthen v t tt =
  match tt with
  | Base b -> Base (Env.strengthen v t b)
  | Ref (b, r) ->
    if mem v b && Cduce.subtype (find v b) t then Ref (b, r)
    else Ref (b, Env.strengthen v t r)
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
let rm_ref v t =
  match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (b, r) when mem v b |> not -> Ref (b, Env.rm v r)
  | _ -> failwith "Variable cannot be removed because it is present in a parent environment."
let rec rm_deep v t =
  match t with
  | Base b -> Base (Env.rm v b)
  | Ref (b, r) -> Ref (rm_deep v b, Env.rm v r)
let neg_ref t =
  match t with
  | Base _ -> failwith "Invalid operation."
  | Ref (b, r) ->
    let base = Ref (b, Env.empty) in
    Env.bindings r |>
    List.filter_map (fun (x,t) ->
      refine x (Cduce.neg t) base
    )
let neg_refs ts =
  let merge t1 t2 =
    let rec aux acc lst = match lst with
    | [] -> Some acc
    | (x,t)::lst ->
      let acc = strengthen x t acc in
      if Cduce.is_empty (find x acc) && Cduce.is_empty t |> not
      then None else aux acc lst
    in
    aux t1 (bindings_ref t2)
  in
  let rec aux acc lst =
    match lst with
    | [] -> acc
    | disj::lst ->
      let acc =
        disj |> List.map (fun r2 ->
          acc |> List.filter_map (fun r1 ->
            merge r1 r2
          )
        ) |> List.flatten
      in
      aux acc lst 
  in
  match ts |> List.map neg_ref with
  | [] -> failwith "Invalid operation."
  | acc::lst -> aux acc lst

let leq_ref t1 t2 =
  match t1, t2 with
  | Base _, _ | _, Base _ -> failwith "Invalid operation."
  | Ref (_, r1), Ref (_, r2) -> Env.leq r1 r2
let equiv_ref t1 t2 = leq_ref t1 t2 && leq_ref t2 t1
let leq t1 t2 = Env.leq (to_env t1) (to_env t2)
let equiv t1 t2 = leq t1 t2 && leq t2 t1

let show t =
  match t with
  | Base _ -> "Base"
  | Ref (_, r) -> Env.show r
let pp fmt t =
  match t with
  | Base _ -> Format.fprintf fmt "Base"
  | Ref (_, r) -> Env.pp fmt r
let pp_filtered lst fmt t =
  match t with
  | Base _ -> Format.fprintf fmt "Base"
  | Ref (_, r) -> Env.pp_filtered lst fmt r
