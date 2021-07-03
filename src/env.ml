open Variable

type t = Cduce.typ VarMap.t

let empty = VarMap.empty
let is_empty =  VarMap.is_empty
let contains_empty = VarMap.exists (fun _ t -> Cduce.is_empty t)
let singleton = VarMap.singleton

let add = VarMap.add

let domain vm = VarMap.bindings vm |> List.map fst

let mem = VarMap.mem

let rm = VarMap.remove

let find = VarMap.find

let strengthen v t env =
  let t = Cduce.cap_o t (find v env) in
  add v t env

let cap =
  VarMap.union (fun _ t1 t2 ->
    Some (Cduce.cap_o t1 t2)
    )

let conj lst =
  List.fold_left cap empty lst

let filter = VarMap.filter

let leq env1 env2 =
  VarMap.for_all (fun v t ->
    VarMap.mem v env1 && Cduce.subtype (VarMap.find v env1) t
  ) env2

let equiv env1 env2 = leq env1 env2 && leq env2 env1

let disjoint env1 env2 =
  let dom1 = domain env1 |> VarSet.of_list in
  let dom2 = domain env2 |> VarSet.of_list in
  VarSet.exists (fun v ->
    if VarMap.mem v env1 && VarMap.mem v env2
    then VarMap.find v env2 |> Cduce.disjoint (VarMap.find v env1)
    else false
  ) (VarSet.union dom1 dom2)

let pp fmt env =
  VarMap.bindings env
  |> List.iter (fun (v, t) ->
    Format.fprintf fmt "%a: %a\n" Variable.pp v Cduce.pp t
  )

let show = Format.asprintf "%a" pp

let pp_filtered names fmt env =
  let env = filter (fun v _ -> match Variable.get_name v with
    | None -> false
    | Some str -> List.mem str names) env in
  pp fmt env
