open Variable

exception EnvIsBottom

type t =
| EnvBottom
| EnvOk of Cduce.typ VarMap.t

let empty = EnvOk VarMap.empty
let bottom = EnvBottom
let is_bottom = function EnvBottom -> true | EnvOk _ -> false
let singleton v t = EnvOk (VarMap.singleton v t)

let add v t env =
  match env with
  | EnvBottom -> EnvBottom
  | EnvOk _ when Cduce.is_empty t -> EnvBottom
  | EnvOk env -> EnvOk (VarMap.add v t env)

let domain t =
  match t with
  | EnvBottom -> raise EnvIsBottom
  | EnvOk env -> VarMap.bindings env |> List.map fst

let mem v env =
  match env with
  | EnvBottom -> true
  | EnvOk env -> VarMap.mem v env

let rm v env =
  match env with
  | EnvBottom -> raise EnvIsBottom
  | EnvOk env -> EnvOk (VarMap.remove v env)

let find v env =
  match env with
  | EnvBottom -> Cduce.empty
  | EnvOk env -> VarMap.find v env

let strengthen v t env =
  let t = if mem v env then Cduce.cap t (find v env) else t in
  add v t env

let cap env1 env2 = match env1, env2 with
  | EnvBottom, _ | _, EnvBottom -> EnvBottom
  | EnvOk env1, EnvOk env2 ->
    let bottom = ref false in
    let map = VarMap.union (fun _ t1 t2 ->
      let inter = Cduce.cap t1 t2 in
      (if Cduce.is_empty inter then bottom := true) ;
      Some inter
      ) env1 env2
    in
    if !bottom then EnvBottom else EnvOk map

let conj lst =
  List.fold_left cap empty lst


let leq env1 env2 =
  match env1, env2 with
  | EnvBottom, _ -> true
  | _, EnvBottom -> false
  | EnvOk env1, EnvOk env2 ->
    VarMap.for_all (fun v t ->
      VarMap.mem v env1 && Cduce.subtype (VarMap.find v env1) t
    ) env2

let equiv env1 env2 = leq env1 env2 && leq env2 env1

let pp fmt env =
  match env with
  | EnvBottom -> Format.fprintf fmt "Bottom\n"
  | EnvOk env ->
    VarMap.bindings env
    |> List.iter (fun (v, t) ->
      Format.fprintf fmt "%a: %a\n" Variable.pp v Cduce.pp t
    )

let show = Format.asprintf "%a" pp
