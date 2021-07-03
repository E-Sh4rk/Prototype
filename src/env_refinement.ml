open Variable

type t = Env.t (* Base *) * Env.t (* Refinement *)

let empty b = (b, Env.empty)
let is_empty (_,r) = Env.is_empty r

let refined_domain (_, r) = Env.domain r
let domain (b,r) =
  let d1 = Env.domain b |> VarSet.of_list in
  let d2 = Env.domain r |> VarSet.of_list in
  VarSet.union d1 d2 |> VarSet.elements

let mem v (b,r) = Env.mem v b || Env.mem v r
let find v (b, r) =
  if Env.mem v r then Env.find v r
  else Env.find v b

let strengthen v t (b,r) =
  if Env.mem v r then (b, Env.strengthen_strict v t r)
  else if Env.mem v b then begin
    let ot = Env.find v b in
    if Cduce.subtype ot t then (b, r)
    else (b, Env.add v (Cduce.cap_o t ot) r)
  end
  else (b, Env.add v t r)

let strengthen_strict v t (b,r) =
  if Env.mem v r then (b, Env.strengthen_strict v t r)
  else begin
    let ot = Env.find v b in
    if Cduce.subtype ot t then (b, r)
    else (b, Env.add v (Cduce.cap_o t ot) r)
  end

let rm v (b,r) = (Env.rm v b, Env.rm v r)

let show (_,r) = Env.show r
let pp fmt (_,r) = Env.pp fmt r
let pp_filtered lst fmt (_,r) = Env.pp_filtered lst fmt r
