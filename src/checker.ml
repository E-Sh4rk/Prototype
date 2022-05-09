
let regroup v res =
  let gammas = res
  |> List.map (fun (gamma,_) -> Env_refinement.rm v gamma)
  |> Utils.remove_duplicates Env_refinement.equiv
  in
  gammas |> List.map (fun gamma ->
    let anns = res |> List.filter_map (fun (gamma', o) ->
      let vt = Env_refinement.find v gamma' in
      let gamma' = Env_refinement.rm v gamma' in
      if Env_refinement.leq gamma gamma'
      then Some (vt, o)
      else None
    ) in
    (gamma, anns)
  )
