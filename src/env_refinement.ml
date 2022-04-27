open Variable

type t = Env.t (* Base *) * Env.t (* Refinement *)

let empty b = (b, Env.empty)
let is_empty (_,r) = Env.is_empty r

let refined_domain (_, r) = Env.domain r
let has_refinement v (_,r) = Env.mem v r

let domain (b,r) =
  let d1 = Env.domain b |> VarSet.of_list in
  let d2 = Env.domain r |> VarSet.of_list in
  VarSet.union d1 d2 |> VarSet.elements

let mem v (b,r) = Env.mem v b || Env.mem v r
let find v (b, r) =
  if Env.mem v r then Env.find v r
  else Env.find v b

let strengthen v t (b,r) =
  if Env.mem v r then (b, Env.strengthen_existing v t r)
  else if Env.mem v b then begin
    let ot = Env.find v b in
    if Cduce.subtype ot t then (b, r)
    else (b, Env.add v (Cduce.cap_o t ot) r)
  end else (b, Env.add v t r)

let refine_existing v t (b,r) =
  try
    let ot = find v (b,r) in
    if (Cduce.is_empty ot |> not) && Cduce.disjoint t ot then None
    else Some (strengthen v t (b,r))
  with Not_found -> None

let refine v t (b,r) =
  if mem v (b,r) then
    let ot = find v (b,r) in
    if (Cduce.subtype Cduce.any_or_absent ot |> not) &&
       (Cduce.is_empty ot |> not) && Cduce.disjoint t ot
    then None
    else Some (strengthen v t (b,r))
  else
    (*Some (strengthen v t (b, r))*)
    assert false

let rm v (b,r) = (Env.rm v b, Env.rm v r)

let to_env (b,r) =
  List.fold_left (fun b x ->
      let t = Env.find x r in
      Env.add x t b
    ) b (Env.domain r)

let show (_,r) = Env.show r
let pp fmt (_,r) = Env.pp fmt r
let pp_filtered lst fmt (_,r) = Env.pp_filtered lst fmt r
