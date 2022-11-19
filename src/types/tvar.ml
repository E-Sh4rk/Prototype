
module CD = Cduce_types

module TVar = struct
  type t = Cduce_types.Var.t

  type vardata = {
    poly: bool;
    infer: bool ;
    dname: string
  }

  module VH = Hashtbl.Make(CD.Var)
  let data = VH.create 100

  module SM = Map.Make(String)
  let lookup = ref SM.empty

  let is_unregistered t =
    VH.mem data t |> not

  let is_poly t = (VH.find data t).poly
  let is_mono t = is_poly t |> not
  let can_infer t = (VH.find data t).infer

  let equal = CD.Var.equal
  let compare = CD.Var.compare
  let name = CD.Var.name
  let display_name t = (VH.find data t).dname

  let unique_mono_id =
    let last = ref 0 in
    (fun () ->
      last := !last + 1 ; !last)

  let unique_poly_id =
    let last = ref 0 in
    (fun () ->
      last := !last + 1 ; !last)

  let mk_mono ?(infer=true) name =
    let id = unique_mono_id () in
    let norm_name = "M"^(string_of_int id) in
    let name = match name with None -> norm_name | Some str -> str in
    let var = CD.Var.mk norm_name in
    VH.add data var {poly=false; infer; dname=name} ;
    lookup := SM.add norm_name var (!lookup) ;
    var
  let mk_poly name =
    let id = unique_poly_id () in
    let norm_name = "P"^(string_of_int id) in
    let name = match name with None -> norm_name | Some str -> str in
    let var = CD.Var.mk norm_name in
    VH.add data var {poly=true; infer=true; dname=name} ;
    lookup := SM.add norm_name var (!lookup) ;
    var

  let lookup str =
    SM.find_opt str (!lookup)

  let typ = CD.Types.var

  let pp = CD.Var.print
end

module type TVarSet = sig
  type t
  val empty : t
  val construct : TVar.t list -> t
  val is_empty : t -> bool
  val mem : t -> TVar.t -> bool
  val filter : (TVar.t -> bool) -> t -> t
  val union : t -> t -> t
  val add : TVar.t -> t -> t
  val inter : t -> t -> t
  val diff : t -> t -> t
  val rm : TVar.t -> t -> t
  val destruct : t -> TVar.t list
  val pp : Format.formatter -> t -> unit
end
module TVarSet = struct
  type t = CD.Var.Set.t
  let empty = CD.Var.Set.empty
  let construct = CD.Var.Set.from_list
  let is_empty = CD.Var.Set.is_empty
  let mem = CD.Var.Set.mem
  let filter = CD.Var.Set.filter
  let union = CD.Var.Set.cup
  let add = CD.Var.Set.add
  let inter = CD.Var.Set.cap
  let diff = CD.Var.Set.diff
  let rm = CD.Var.Set.remove
  let destruct = CD.Var.Set.get
  let pp fmt t =
    destruct t |> Format.fprintf fmt "%a@." (Utils.pp_list TVar.pp)
end

type subst = CD.Types.Subst.t
module type Subst = sig
  type t = subst
  val construct : (TVar.t * Base.typ) list -> t
  val identity : t
  val is_identity : t -> bool
  val dom : t -> TVarSet.t
  val mem : t -> TVar.t -> bool
  val rm: TVar.t -> t -> t
  val find : t -> TVar.t -> Base.typ
  val equiv : t -> t -> bool
  val apply : t -> Base.typ -> Base.typ
  val destruct : t -> (TVar.t * Base.typ) list
  val pp : Format.formatter -> t -> unit
end
module Subst = struct
  type t = subst
  let is_id (v,t) =
    match CD.Types.Subst.check_var t with
    | `Pos v' when CD.Var.equal v v' -> true
    | _ -> false
  let normalize = CD.Var.Map.filter (fun v t -> is_id (v,t) |> not)
  let construct lst =
    lst |> CD.Types.Subst.from_list |> normalize
  let identity = CD.Types.Subst.from_list []
  let destruct = CD.Var.Map.get
  let is_identity t = destruct t |> List.for_all is_id
  let apply = CD.Types.Subst.apply
  let dom s = CD.Var.Map.domain s
  let mem s v = CD.Var.Set.mem (dom s) v
  let rm = CD.Var.Map.remove
  let find s v = CD.Var.Map.assoc v s
  let equiv s1 s2 =
    let s1 = normalize s1 in
    let s2 = normalize s2 in
    CD.Var.Map.equal Base.equiv s1 s2
  (* let pp_entry fmt (v,t) =
    Format.fprintf fmt "%a ===> %a" pp_var v pp_typ t
  let pp fmt t =
    Format.fprintf fmt "%a@." (Utils.pp_long_list pp_entry) (destruct t) *)
  let pp = CD.Types.Subst.print
end

let vars = CD.Types.Subst.vars
let top_vars = CD.Types.Subst.top_vars
let vars_with_polarity t = CD.Types.Subst.var_polarities t |> CD.Var.Map.get
let check_var = CD.Types.Subst.check_var

let generalize mono t =
  let is_mono v = TVar.is_unregistered v || TVar.is_mono v in
  let s = TVarSet.diff (vars t) mono |>
    TVarSet.filter is_mono |>
    TVarSet.destruct |> List.map (fun v ->
      (v, TVar.mk_poly None |> TVar.typ)
    ) |> Subst.construct in
  Subst.apply s t
let monomorphize_fresh t =
  let is_poly v = TVar.is_unregistered v || TVar.is_poly v in
  let s = vars t |>
    TVarSet.filter is_poly |>
    TVarSet.destruct |> List.map (fun v ->
      (v, TVar.mk_mono None |> TVar.typ)
    ) |> Subst.construct in
  Subst.apply s t
let monomorphize = failwith "TODO"