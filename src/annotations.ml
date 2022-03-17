
let partition_aux lst is_empty disjoint cap diff =
  let rec aux lst =
    let rm_empty = List.filter (fun t -> is_empty t |> not) in
    let inter t1 t2 =
      if disjoint t1 t2 then t1 else cap t1 t2
    in
    match rm_empty lst with
    | [] -> []
    | t::lst ->
      let s = List.fold_left inter t lst in
      let lst = (t::lst)
      |> List.map (fun t -> diff t s)
      |> aux
      in
      s::lst
  in aux lst

let partition t lst =
  if Cduce.is_empty t then [Cduce.empty]
  else
    let lst = List.map (Cduce.cap_o t) lst in
    partition_aux (t::lst) Cduce.is_empty Cduce.disjoint Cduce.cap_o Cduce.diff

let partition_for_full_domain lst =
  match partition_aux lst Cduce.is_empty Cduce.disjoint Cduce.cap_o Cduce.diff with
  | [] -> [Cduce.empty]
  | lst -> lst

module VarAnnot = struct
  type t = (Env.t * Cduce.typ) list
  let empty = []
  let any = [Env.empty, Cduce.any]
  let initial_lambda ~legacy = if legacy then any else empty
  let initial_binding ~legacy = if legacy then any else empty
  let is_empty va = va = []

  let singleton env t = [(env, t)]

  let full_domain t =
    List.map snd t |> Types_additions.disj

  let size t = List.length t

  let splits env va =
    List.filter (fun (env',_) -> Env.leq env env') va
    |> List.map snd
    (*|> Utils.remove_duplicates Cduce.equiv*)

  let splits_or d env va =
    let res = splits env va in
    if res = [] then [d] else res

  let add_split env typ va =
    let splits = splits env va in
    if List.exists (fun t -> Cduce.equiv t typ) splits
    then va
    else (env, typ)::va

  let restrict env anns =
    let dom = Env.domain env |> Variable.VarSet.of_list in
    anns |>
    List.filter (fun (aenv, _) ->
      Env.domain aenv |> Variable.VarSet.of_list |> Variable.VarSet.inter dom |>
      Variable.VarSet.for_all (fun v ->
        let t1 = Env.find v env in
        let t2 = Env.find v aenv in
        Cduce.is_empty t1 || (Cduce.cap t1 t2 |> Cduce.is_empty |> not)
        )
      ) |>
    List.map (fun (gamma, t) -> (Env.cap env gamma, t))

  let cup va1 va2 =
    List.fold_left (fun acc (env, typ) -> add_split env typ acc) va1 va2

  let union lst =
    List.fold_left cup [] lst

  let pp_filtered names fmt t =
    List.iter (
      fun (env, t) ->
        Format.fprintf fmt "---------------@.Type: %a@.Env: %a@.---------------@."
        Cduce.pp_typ t (Env.pp_filtered names) env
    ) t

  let pp fmt t =
    Format.fprintf fmt "[%i]" (List.length t)
end
