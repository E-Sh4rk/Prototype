open Variable

module VarAnnot = struct
  type t = (Env.t * Cduce.typ) list
  let empty = []
  let splits env ?(initial=Cduce.any) va =
    List.filter (fun (env',_) -> Env.leq env env') va
    |> List.map (fun (_,snd) -> Cduce.cap snd initial)
    |> List.filter (fun t -> Cduce.is_empty t |> not)
  let add_split env typ va = (env, typ)::va
end

module Annotations = struct
  type t = VarAnnot.t VarMap.t
  let empty = VarMap.empty

  let mem_var = VarMap.mem
  let add_var = VarMap.add
  let remove_var = VarMap.remove
  let get_var = VarMap.find

  let splits v env ?(initial=Cduce.any) annots =
    if mem_var v annots
    then get_var v annots |> VarAnnot.splits env ~initial
    else [initial]
  
  let add_split v env typ annots =
    let va = if mem_var v annots then get_var v annots else VarAnnot.empty in
    let va = VarAnnot.add_split env typ va in
    add_var v va annots
end
