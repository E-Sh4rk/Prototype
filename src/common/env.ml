open Parsing.Variable
open Types.Base
open Types.Tvar

type t = typ VarMap.t * TVarSet.t

let empty = (VarMap.empty, TVarSet.empty)
let is_empty (m,_) =  VarMap.is_empty m
let singleton v t = (VarMap.singleton v t, vars t)
let construct lst = (VarMap.of_seq (List.to_seq lst),
  List.map snd lst |> List.map vars |> TVarSet.union_many)

let add v t (m,s) = (VarMap.add v t m, TVarSet.union s (vars t))

let domain (m, _) = VarMap.bindings m |> List.map fst

let bindings (m, _) = VarMap.bindings m

let mem v (m, _) = (VarMap.mem v m)

let mem_not_absent v (m, _) =
  VarMap.mem v m && has_absent (VarMap.find v m) |> not

let reconstruct m = VarMap.bindings m |> construct

let rm v (m, _) = VarMap.remove v m |> reconstruct

let find v (m, _) = VarMap.find v m

let strengthen_existing v t env =
  let t = cap_o t (find v env) in
  add v t env

let strengthen v t env =
  try strengthen_existing v t env with Not_found -> add v t env

let cap (m1, s1) (m2, s2) =
  (VarMap.union (fun _ t1 t2 ->
    Some (cap_o t1 t2)
    ) m1 m2,
  TVarSet.union s1 s2)

let conj lst =
  List.fold_left cap empty lst

let filter f (m, _) = VarMap.filter f m |> reconstruct

let leq (m1,_) (m2,_) =
  VarMap.for_all (fun v t ->
    VarMap.mem v m1 && subtype (VarMap.find v m1) t
  ) m2

let equiv env1 env2 = leq env1 env2 && leq env2 env1

let pp fmt (m, _) =
  VarMap.bindings m
  |> List.iter (fun (v, t) ->
    Format.fprintf fmt "%a: %a\n" Variable.pp v pp t
  )

let show = Format.asprintf "%a" pp

let pp_filtered names fmt env =
  let env = filter (fun v _ -> match Variable.get_name v with
    | None -> false
    | Some str -> List.mem str names) env in
  pp fmt env

let add v t e = assert (mem v e |> not) ; add v t e

let tvars (_, s) = s