open Variable

module VarAnnot = struct
  type t = (Env.t * Cduce.typ) list
  let empty = []
  let is_empty va = va = []

  let rec partition lst =
    let inter t1 t2 =
      if Cduce.disjoint t1 t2 then t1 else Cduce.cap t1 t2
    in
    match lst with
    | [] -> []
    | t::lst ->
      let s = List.fold_left inter t lst in
      let lst = (t::lst)
      |> List.map (fun t -> Cduce.diff t s)
      |> List.filter (fun t -> Cduce.is_empty t |> not)
      in
      s::(partition lst)

  let splits env ?(initial=Cduce.any) va =
    let res =
      List.filter (fun (env',_) -> Env.leq env env') va
      |> List.map (fun (_,snd) -> Cduce.cap snd initial)
      |> List.filter (fun t -> Cduce.is_empty t |> not)
      |> partition
    in
    if res = [] then [initial] else res

  let splits_strict env va =
    List.filter (fun (env',_) -> Env.leq env env') va
    |> List.map snd
    |> Utils.remove_duplicates Cduce.equiv

  let add_split env typ va =
    let splits = splits env va in
    if List.exists (fun t -> Cduce.equiv t typ) splits
    then va
    else (env, typ)::va

  let cup va1 va2 =
    List.fold_left (fun acc (env, typ) -> add_split env typ acc) va1 va2

  let pp_filtered names fmt t =
    List.iter (
      fun (env, t) ->
        Format.fprintf fmt "---------------@.Type: %a@.Env: %a@.---------------@."
        Cduce.pp_typ t (Env.pp_filtered names) env
    ) t
end

module Annotations = struct
  type t = VarAnnot.t VarMap.t
  let empty = VarMap.empty

  let mem_var = VarMap.mem
  let add_var = VarMap.add
  let remove_var = VarMap.remove
  let get_var = VarMap.find

  let is_empty v t =
    if mem_var v t
    then (get_var v t |> VarAnnot.is_empty)
    else true

  let restrict vs annots =
    VarSet.fold (fun v acc ->
      if mem_var v annots
      then VarMap.add v (get_var v annots) acc
      else acc
    )
    vs VarMap.empty

  let splits v env ?(initial=Cduce.any) annots =
    if mem_var v annots
    then get_var v annots |> VarAnnot.splits env ~initial
    else [initial]

  let splits_strict v env annots =
    if mem_var v annots
    then get_var v annots |> VarAnnot.splits_strict env
    else []
  
  let add_split v env typ annots =
    let va = if mem_var v annots then get_var v annots else VarAnnot.empty in
    let va = VarAnnot.add_split env typ va in
    add_var v va annots

  let cup a1 a2 =
    VarMap.union (fun _ va1 va2 -> Some (VarAnnot.cup va1 va2)) a1 a2

  let union lst =
    List.fold_left cup empty lst
end
