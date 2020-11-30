open Variable

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

let mem v env =
  match env with
  | EnvBottom -> true
  | EnvOk env -> VarMap.mem v env

let rm v env =
  match env with
  | EnvBottom -> EnvBottom
  | EnvOk env -> EnvOk (VarMap.remove v env)

let find v env =
  match env with
  | EnvBottom -> Cduce.empty
  | EnvOk env -> VarMap.find v env

let from_map map =
  if List.exists (fun (_,t) -> Cduce.is_empty t) (VarMap.bindings map)
  then EnvBottom else EnvOk map

let cap env1 env2 = match env1, env2 with
  | EnvBottom, _ | _, EnvBottom -> EnvBottom
  | EnvOk env1, EnvOk env2 ->
    from_map (VarMap.union (fun _ t1 t2 -> Some (Cduce.cap t1 t2)) env1 env2)

let conj lst =
  List.fold_left cap empty lst

let pp fmt env =
  match env with
  | EnvBottom -> Format.fprintf fmt "Bottom\n"
  | EnvOk env ->
    VarMap.bindings env
    |> List.iter (fun (v, t) ->
      Format.fprintf fmt "%a: %a\n" Variable.pp v Cduce.pp t
    )

let show = Format.asprintf "%a" pp
