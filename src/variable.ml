module Variable = struct

  let data = Hashtbl.create 100

  type t = int
  let compare = compare
  let equals a b = a = b

  let next_id =
    let last = ref 0 in
    fun () ->
      last := !last + 1 ;
      !last

  let create display_name =
    let id = next_id () in
    Hashtbl.add data id (display_name, []) ;
    id

  let attach_location id loc =
    let (name, locs) = Hashtbl.find data id in
    Hashtbl.replace data id (name, loc::locs)

  let get_locations id =
    let (_, locs) = Hashtbl.find data id
    in locs

  let get_name id =
    let (name, _) = Hashtbl.find data id
    in name
end

module VarMap = Map.Make(Variable)
module VarSet = Set.Make(Variable)