
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

  let unique_unregistered_id =
    let last = ref 0 in
    (fun () ->
      last := !last + 1 ; !last)

  let mk_mono ?(infer=true) name =
    let id = unique_mono_id () in
    let norm_name = (string_of_int id)^"M" in
    let name = match name with None -> norm_name | Some str -> str in
    let var = CD.Var.mk norm_name in
    VH.add data var {poly=false; infer; dname=name} ;
    lookup := SM.add norm_name var (!lookup) ;
    var
  let mk_poly name =
    let id = unique_poly_id () in
    let norm_name = (string_of_int id)^"P" in
    let name = match name with None -> norm_name | Some str -> str in
    let var = CD.Var.mk norm_name in
    VH.add data var {poly=true; infer=true; dname=name} ;
    lookup := SM.add norm_name var (!lookup) ;
    var
  let mk_fresh t =
    let dname = display_name t in
    if is_mono t then mk_mono (Some dname) else mk_poly (Some dname)
  let mk_unregistered () =
    let id = unique_unregistered_id () in
    let norm_name = (string_of_int id)^"U" in
    CD.Var.mk norm_name

  let lookup str =
    SM.find_opt str (!lookup)

  let typ = CD.Types.var

  let pp = CD.Var.print
end

module TVarSet = struct
  type t = CD.Var.Set.t
  let empty = CD.Var.Set.empty
  let construct = CD.Var.Set.from_list
  let is_empty = CD.Var.Set.is_empty
  let mem = CD.Var.Set.mem
  let filter = CD.Var.Set.filter
  let union = CD.Var.Set.cup
  let union_many = List.fold_left union empty
  let add = CD.Var.Set.add
  let inter = CD.Var.Set.cap
  let inter_many = List.fold_left inter empty
  let diff = CD.Var.Set.diff
  let rm = CD.Var.Set.remove
  let destruct = CD.Var.Set.get
  let pp fmt t =
    destruct t |> Format.fprintf fmt "%a@." (Utils.pp_list TVar.pp)
end

let vars = CD.Types.Subst.vars
let check_var = CD.Types.Subst.check_var

module Subst = struct
  type t = CD.Types.Subst.t
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
  let find' t v = if mem t v then find t v else TVar.typ v
  let equiv s1 s2 =
    let s1 = normalize s1 in
    let s2 = normalize s2 in
    CD.Var.Map.equal Base.equiv s1 s2

  let apply_to_subst s2 s1 =
    destruct s1 |>
      List.map (fun (v,t) -> (v, apply s2 t))
  let compose s2 s1 =
      let only_s2 = destruct s2 |>
          List.filter (fun (v, _) -> mem s1 v |> not) in
      construct ((apply_to_subst s2 s1)@only_s2)
  let apply_to_subst s2 s1 = apply_to_subst s2 s1 |> construct
  let combine s1 s2 =
      assert (TVarSet.inter (dom s1) (dom s2) |> TVarSet.is_empty) ;
      let s1 = destruct s1 in
      let s2 = destruct s2 in
      s1@s2 |> construct
  let restrict s vars =
      let vars = TVarSet.inter (dom s) vars in
      vars |> TVarSet.destruct |> List.map (fun v -> (v, find s v)) |> construct
  let remove s vars =
      let nvars = TVarSet.diff (dom s) vars in
      restrict s nvars
  let split s vars =
      (restrict s vars, remove s vars)
  let codom s =
      destruct s |> List.map (fun (_, t) -> vars t)
      |> TVarSet.union_many
  let is_renaming t =
    destruct t |>
    List.for_all (fun (_,t) ->
      match check_var t with
      | `Pos _ -> true
      | _ -> false)
  let inverse_renaming t =
    destruct t |>
    List.map (fun (v,t) ->
      match check_var t with
      | `Pos v' -> (v', TVar.typ v)
      | _ -> assert false) |>
    construct

(* let pp_entry fmt (v,t) =
    Format.fprintf fmt "%a ===> %a" pp_var v pp_typ t
  let pp fmt t =
    Format.fprintf fmt "%a@." (Utils.pp_long_list pp_entry) (destruct t) *)
  let pp = CD.Types.Subst.print
end

let vars_mono t =
  TVarSet.filter TVar.is_mono (vars t)
let vars_poly t =
  TVarSet.filter TVar.is_poly (vars t)
let vars_infer t =
  TVarSet.filter TVar.can_infer (vars t)
let top_vars = CD.Types.Subst.top_vars
let vars_with_polarity t = CD.Types.Subst.var_polarities t |> CD.Var.Map.get
let is_mono_typ t =
  vars_poly t |> TVarSet.is_empty

let refresh ~mono vars =
  let test = if mono then TVar.is_mono else TVar.is_poly in
  let f = (fun v -> (v, TVar.mk_fresh v |> TVar.typ)) in
  vars |> TVarSet.filter test |>
    TVarSet.destruct |> List.map f |> Subst.construct
let refresh_all vars =
  let f = (fun v -> (v, TVar.mk_fresh v |> TVar.typ)) in
  vars |> TVarSet.destruct |> List.map f |> Subst.construct
let generalize vars =
  vars |>
    TVarSet.filter TVar.is_mono |>
    TVarSet.destruct |> List.map (fun v ->
      (v, TVar.mk_poly None |> TVar.typ)
    ) |> Subst.construct

let monomorphize vars =
  vars |>
    TVarSet.filter TVar.is_poly |>
    TVarSet.destruct |> List.map (fun v ->
      (v, TVar.mk_mono None |> TVar.typ)
    ) |> Subst.construct

let lookup_or_fresh c v =
  let str = TVar.name v in
  match TVar.lookup str with
  | Some v' -> Some v'
  | None ->
    let str = (List.hd (String.split_on_char c str))^(String.make 1 c) in
    begin match TVar.lookup str with
    | Some v' -> Some v'
    | None -> None
    end
let lookup_or_fresh v =
  match lookup_or_fresh 'M' v with
  | Some v' -> Some v'
  | None -> lookup_or_fresh 'P' v
let lookup_unregistered vars =
  vars |>
    TVarSet.filter TVar.is_unregistered |>
    TVarSet.destruct |> List.filter_map (fun v ->
      match lookup_or_fresh v with None -> None
      | Some v' -> Some (v, TVar.typ v')
    ) |> Subst.construct

let register_unregistered ~mono vars =
  let f =
    if mono
    then (fun v -> (v, TVar.mk_mono None |> TVar.typ))
    else (fun v -> (v, TVar.mk_poly None |> TVar.typ))
  in
  vars |>
    TVarSet.filter TVar.is_unregistered |>
    TVarSet.destruct |> List.map f |> Subst.construct

(* Operations on types *)
module Iter = Base.Iter
module type Kind = Base.Kind

module Raw = struct
(* let subst_vars_with delta s t =
  let vars = TVarSet.diff (vars t) delta in
  let subst = vars |> TVarSet.destruct |>
    List.map (fun v -> (v,s)) |> Subst.construct in
  Subst.apply subst t *)

  let inf_typ delta t =
    CD.Types.Subst.min_type delta t (* TODO: This implem is not optimal *)
    (* CD.Types.Subst.clean_type ~pos:empty ~neg:any delta t |>
    subst_vars_with delta any *)
  
  let sup_typ delta t =
    CD.Types.Subst.max_type delta t (* TODO: This implem is not optimal *)
    (* CD.Types.Subst.clean_type ~pos:any ~neg:empty delta t |>
    subst_vars_with delta any *)
  
  (* Tallying *)
  let clean_type ~pos ~neg vars t =
    CD.Types.Subst.clean_type ~pos ~neg vars t
  let clean_type_subst ~pos ~neg mono t =
    let subst =
        vars_with_polarity t |>
        List.filter_map (fun (v,p) ->
            if TVarSet.mem mono v then None
            else match p with
            | `Pos -> Some (v, pos)
            | `Neg -> Some (v, neg)
            | `Both -> None
        )
    in
    Subst.construct subst
  let rectype = CD.Types.Subst.solve_rectype
  let tallying_raw ~var_order = CD.Types.Tallying.tallying ~var_order

  let print_tallying_instance var_order delta constr =
    Format.printf "Constraints:@." ;
    let allvars = ref TVarSet.empty in
    constr |> List.iter (fun (l,r) ->
        allvars := TVarSet.union (!allvars) (vars l) ;
        allvars := TVarSet.union (!allvars) (vars r) ;
        Format.printf "(%a, %a)@." Base.pp_typ l Base.pp_typ r ;
    );
    Format.printf "With delta=%a, var order=%a, and natural var order=%a@."
        (Utils.pp_list TVar.pp) (TVarSet.destruct delta)
        (Utils.pp_list TVar.pp) var_order
        (Utils.pp_list TVar.pp) (TVarSet.destruct !allvars)

  let check_tallying_solution var_order delta constr res =
    let error = ref false in
    let res =
        res |> List.filter_map (fun s ->
        if (constr |> List.for_all (fun (l,r) ->
                Base.subtype (Subst.apply s l) (Subst.apply s r)
            ))
        then Some s else begin
            error := true ;
            Format.printf "INVALID SOLUTION REMOVED: %a@." Subst.pp s ;
            None
        end
    )
    in
    if !error then begin
        Format.printf "WARNING: Cduce tallying issue.@." ;
        print_tallying_instance var_order delta constr
    end ; res

  let tallying_infer poly noninfered constr =
    assert (TVarSet.inter (TVarSet.construct poly) noninfered |> TVarSet.is_empty) ;
    Utils.log ~level:2 "Tallying (inference) instance initiated...@?" ;
    let res = tallying_raw ~var_order:poly noninfered constr in
    Utils.log ~level:2 " Done (%i sol).@." (List.length res) ;
    res |> check_tallying_solution poly noninfered constr

  let tallying mono constr =
    Utils.log ~level:2 "Tallying (no inference) instance initiated...@?" ;
    let var_order = [] in
    let res = tallying_raw ~var_order mono constr in
    Utils.log ~level:2 " Done (%i sol).@." (List.length res) ;
    res |> check_tallying_solution [] mono constr
end

let clean_type ~pos ~neg t =
  Raw.clean_type ~pos ~neg (vars_mono t) t

let clean_type_subst ~pos ~neg t =
  vars_with_polarity t |>
  List.filter_map (fun (v,p) ->
      if TVar.is_mono v then None
      else match p with
      | `Pos -> Some (v, pos)
      | `Neg -> Some (v, neg)
      | `Both -> None
  ) |> Subst.construct

let tallying constr =
  let mono = constr |>
    List.map (fun (a,b) -> [vars_mono a ; vars_mono b]) |>
    List.flatten in
  let mono = TVarSet.union_many mono in
  let res = Raw.tallying_raw ~var_order:[] mono constr in
  let codom = List.map Subst.codom res in
  let codom = TVarSet.union_many codom in
  let lkp_subst = lookup_unregistered codom in
  let reg_subst = register_unregistered ~mono:false codom in
  res
    |> List.map (Subst.apply_to_subst lkp_subst)
    |> List.map (Subst.apply_to_subst reg_subst)

let tallying_infer constr =
  (* TODO: set var_order for the tallying instance *)
  (* TODO: make newly introduced mono vars more deterministic? *)
  let infer = constr |>
    List.map (fun (a,b) -> [vars_infer a ; vars_infer b]) |>
    List.flatten in
  let infer = TVarSet.union_many infer in
  let gen = generalize infer in
  let mon = Subst.inverse_renaming gen in
  let constr = constr |>
    List.map (fun (a,b) ->
      let r1 = refresh_all (vars_poly a) in
      let r2 = refresh_all (vars_poly b) in
      let a = Subst.apply r1 a in
      let b = Subst.apply r2 b in
      (Subst.apply gen a, Subst.apply gen b))
  in
  tallying constr |> List.map (fun s ->
    let s = Subst.apply_to_subst s gen in
    let s = Subst.apply_to_subst mon s in
    let mono_subst = monomorphize (Subst.codom s) in
    Subst.apply_to_subst mono_subst s
  )

(* Some additions *)
let factorize (pvs, nvs) t =
  let open Iter in
  let treat_kind m t =
    let module K = (val m : Kind) in
    let conj lst = match lst with
    | [] -> K.Dnf.any
    | a::lst -> List.fold_left K.Dnf.cap a lst
    in
    let disj lst = match lst with
    | [] -> K.Dnf.empty
    | a::lst -> List.fold_left K.Dnf.cup a lst
    in
    let rebuild_partial lst =
      lst |> List.map (fun ((pvs, nvs), mono) ->
        let pvs = TVarSet.destruct pvs in
        let nvs = TVarSet.destruct nvs in
        let t = K.Dnf.mono mono in
        let pvs = pvs |> List.map K.Dnf.var |> conj in
        let nvs = nvs |> List.map K.Dnf.var |> List.map K.Dnf.neg |> conj in
        conj [pvs ; nvs ; t]
      ) |> disj
    in
    let (a,b) =
      K.get_vars t
      |> K.Dnf.get_partial |> List.map (fun ((pvs',nvs'), mono) ->
        let pvs' = TVarSet.construct pvs' in
        let nvs' = TVarSet.construct nvs' in
        if TVarSet.diff pvs pvs' |> TVarSet.is_empty &&
            TVarSet.diff nvs nvs' |> TVarSet.is_empty
        then
          let pvs' = TVarSet.diff pvs' pvs in
          let nvs' = TVarSet.diff nvs' nvs in
          ([((pvs',nvs'),mono)], [])
        else ([], [((pvs',nvs'),mono)])
      ) |> List.split in
    let (a,b) = (List.concat a, List.concat b) in
    let (a,b) = (rebuild_partial a, rebuild_partial b) in
    (K.mk a, K.mk b)
  in
  let t = fold (fun (a,b) pack t ->
      let (a',b') = match pack with
      | Absent -> (Base.empty, Base.absent)
      | Abstract m | Char m | Int m | Atom m -> treat_kind m t
      | Times m ->
          let module K = (val m :> Kind) in
          treat_kind (module K) t
      | Xml m ->
          let module K = (val m :> Kind) in
          treat_kind (module K) t
      | Function m ->
          let module K = (val m :> Kind) in
          treat_kind (module K) t
      | Record m ->
          let module K = (val m :> Kind) in
          treat_kind (module K) t
      in
      (Base.cup a a', Base.cup b b')
    ) (Base.empty, Base.empty) t
  in t
