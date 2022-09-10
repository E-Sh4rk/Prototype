open Types.Base

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

  let pp fmt t =
    match get_name t with
    | None -> Format.fprintf fmt "%d" t
    | Some str -> Format.fprintf fmt "%s" str
    
  let show t =
    match get_name t with
    | None -> string_of_int t
    | Some str -> str

  let typevars = Hashtbl.create 100

  let to_typevar v =
    if Hashtbl.mem typevars v
    then Hashtbl.find typevars v
    else
      let tv = mk_var (show v) in
      Hashtbl.add typevars v tv ;
      tv

  let typevars_ext = Hashtbl.create 100

  let get_typevar v i =
    if Hashtbl.mem typevars_ext (v,i)
    then Hashtbl.find typevars_ext (v,i)
    else
      let tv = mk_var ((show v)^"_"^(string_of_int i)) in
      Hashtbl.add typevars_ext (v,i) tv ;
      tv
end

let predefined_vars = Hashtbl.create 100

let get_predefined_var i =
  if Hashtbl.mem predefined_vars i
  then Hashtbl.find predefined_vars i
  else
    let v = Variable.create None in
    Hashtbl.add predefined_vars i v ;
    v

module VarMap = Map.Make(Variable)
module VarSet = Set.Make(Variable)