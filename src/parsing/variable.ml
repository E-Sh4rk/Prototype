open Types.Tvar

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

  let create ~binding ~lambda display_name =
    let id = next_id () in
    Hashtbl.add data id (display_name, [], binding, lambda) ;
    id

  let create_binding display_name =
    create ~binding:true ~lambda:false display_name

  let create_lambda display_name =
    create ~binding:false ~lambda:true display_name

  let create_other display_name =
    create ~binding:false ~lambda:false display_name

  let attach_location id loc =
    let (name, locs, b, l) = Hashtbl.find data id in
    Hashtbl.replace data id (name, loc::locs, b, l)

  let get_locations id =
    let (_, locs, _, _) = Hashtbl.find data id
    in locs

  let is_binding_var id =
    let (_, _, b, _) = Hashtbl.find data id
    in b

  let is_lambda_var id =
    let (_, _, _, l) = Hashtbl.find data id
    in l

  let get_name id =
    let (name, _, _, _) = Hashtbl.find data id
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
      let tv = TVar.mk_mono (Some (show v)) in
      Hashtbl.add typevars v tv ;
      tv

  let typevars_ext = Hashtbl.create 100

  let get_typevar v i =
    if Hashtbl.mem typevars_ext (v,i)
    then Hashtbl.find typevars_ext (v,i)
    else
      let tv = TVar.mk_mono (Some ((show v)^"_"^(string_of_int i))) in
      Hashtbl.add typevars_ext (v,i) tv ;
      tv
end

module VarMap = Map.Make(Variable)
module VarSet = Set.Make(Variable)