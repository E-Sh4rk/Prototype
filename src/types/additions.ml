open Base
open Tvar

module StrMap = Map.Make(String)
module StrSet = Set.Make(String)
module LabelMap = CD.Ident.LabelMap

exception TypeDefinitionError of string

(* Construction of types *)

type type_base =
    | TInt of int option * int option | TSChar of char | TSString of string
    | TBool | TTrue | TFalse | TUnit | TChar | TAny | TEmpty | TNil
    | TString | TList | TFloat

type type_regexp =
    | ReEpsilon | ReEmpty
    | ReType of type_expr
    | ReSeq of type_regexp * type_regexp
    | ReStar of type_regexp
    | ReAlt of type_regexp * type_regexp

and type_expr =
    | TVar of string
    | TBase of type_base
    | TCustom of type_expr list * string
    | TPair of type_expr * type_expr
    | TRecord of bool * (string * type_expr * bool) list
    | TSList of type_regexp
    | TArrow of type_expr * type_expr
    | TCup of type_expr * type_expr
    | TCap of type_expr * type_expr
    | TDiff of type_expr * type_expr
    | TNeg of type_expr

type type_alias = TVar.t list * node
type type_env = type_alias StrMap.t (* User-defined types *) * StrSet.t (* Atoms *)
type var_type_env = typ StrMap.t (* Var types *)

let empty_tenv = (StrMap.empty, StrSet.empty)
let empty_vtenv = StrMap.empty

let type_base_to_typ t =
    match t with
    | TInt (lb,ub) -> interval lb ub
    | TFloat -> float_typ
    | TSChar c -> single_char c
    | TSString str -> single_string str
    | TBool -> bool_typ | TNil -> nil_typ
    | TTrue -> true_typ | TFalse -> false_typ
    | TUnit -> unit_typ | TChar -> char_typ
    | TAny -> any | TEmpty -> empty
    | TString -> string_typ | TList -> list_typ

let instantiate_alias env args name =
    try
        let (params, node) = StrMap.find name env in
        let subst = List.combine params args |> Subst.construct in
        Subst.apply subst (descr node)
    with
    | Not_found -> raise (TypeDefinitionError (Printf.sprintf "Type %s undefined!" name))
    | Invalid_argument _ -> raise (TypeDefinitionError (Printf.sprintf "Wrong arity for type %s!" name))

let infer_prefix = "_"
let is_infer_var_name name =
    String.starts_with ~prefix:infer_prefix name

let derecurse_types env venv defs =
    let open Cduce_core in
    let venv =
        let h = Hashtbl.create 16 in
        StrMap.iter (fun n v -> Hashtbl.add h n v) venv ;
        h
    in
    let henv = Hashtbl.create 16 in
    let () =
        List.iter (fun (name, params, def) ->
                if StrMap.mem name env then 
                    raise (TypeDefinitionError (Printf.sprintf "Type %s already defined!" name))
                else
                    Hashtbl.add henv name (def, params, [])) defs
    in
    let rec get_name ~nd args name =
        match Hashtbl.find henv name with
        | def, params, lst ->
            if nd then raise (TypeDefinitionError (Printf.sprintf "Cannot use a reference to %s here!" name)) ;
            let cached = lst |> List.find_opt (fun (args',_) ->
                try List.for_all2 equiv args args' with Invalid_argument _ -> false) in
            begin match cached with
            | None ->
                begin try
                    let v = Typepat.mk_delayed () in
                    Hashtbl.replace henv name (def, params, (args, v)::lst);
                    let local = List.combine params args |> List.to_seq |> StrMap.of_seq in
                    let t = aux ~nd local def in
                    Typepat.link v t;
                    v
                with Invalid_argument _ ->
                    raise (TypeDefinitionError (Printf.sprintf "Wrong arity for type %s!" name))
                end
            | Some (_, v) -> v
            end
        | exception Not_found -> 
            Typepat.mk_type (instantiate_alias env args name)
    and aux ~nd (* no delayed: disallow relying on delayed vars *) lcl t =
        match t with
        | TVar v ->
            begin match StrMap.find_opt v lcl, Hashtbl.find_opt venv v with
            | Some t, _ | None, Some t -> Typepat.mk_type t
            | None, None ->
                let t = TVar.mk_mono ~infer:(is_infer_var_name v) (Some v) |> TVar.typ in
                Hashtbl.add venv v t ;
                Typepat.mk_type t
            end
        | TBase tb -> Typepat.mk_type (type_base_to_typ tb)
        | TCustom (args, n) ->
            let args = args |> List.map (aux ~nd:true lcl) |> List.map Typepat.typ in
            get_name ~nd args n
        | TPair (t1,t2) -> Typepat.mk_prod (aux ~nd lcl t1) (aux ~nd lcl t2)
        | TRecord (is_open, fields) ->
            let aux' (label,t,opt) =
                let n = aux ~nd lcl t in
                let n = if opt then Typepat.mk_optional n else n in
                (to_label label, (n, None))
            in
            let lmap = 
                Cduce_types.Ident.LabelMap.from_list_disj (List.map aux' fields)
            in
            Typepat.mk_record is_open lmap
        | TSList lst -> Typepat.rexp (aux_re ~nd lcl lst)
        | TArrow (t1,t2) -> Typepat.mk_arrow (aux ~nd lcl t1) (aux ~nd lcl t2)
        | TCup (t1,t2) ->
            let t1 = aux ~nd lcl t1 in
            let t2 = aux ~nd lcl t2 in
            Typepat.mk_or t1 t2
        | TCap (t1,t2) ->
            let t1 = aux ~nd lcl t1 in
            let t2 = aux ~nd lcl t2 in
            Typepat.mk_and t1 t2
        | TDiff (t1,t2) ->
            let t1 = aux ~nd lcl t1 in
            let t2 = aux ~nd lcl t2 in
            Typepat.mk_diff t1 t2
        | TNeg t -> Typepat.mk_diff (Typepat.mk_type any) (aux ~nd lcl t)
    and aux_re ~nd lcl r =
        match r with
        | ReEmpty -> Typepat.mk_empty
        | ReEpsilon -> Typepat.mk_epsilon
        | ReType t -> Typepat.mk_elem (aux ~nd lcl t)
        | ReSeq (r1, r2) -> Typepat.mk_seq (aux_re ~nd lcl r1) (aux_re ~nd lcl r2)
        | ReAlt (r1, r2) -> Typepat.mk_alt (aux_re ~nd lcl r1) (aux_re ~nd lcl r2)
        | ReStar r -> Typepat.mk_star (aux_re ~nd lcl r)
    in
    let res = defs |> List.map (fun (name, params, _) ->
        let params = List.map (fun _ -> TVar.mk_unregistered ()) params in
        let args = List.map TVar.typ params in
        let node = get_name ~nd:false args name in
        (* Typepat.internalize node ; *)
        name, params, Typepat.typ node) in
    let venv = Hashtbl.fold StrMap.add venv StrMap.empty in
    (res, venv)

let type_expr_to_typ (tenv, _) venv t = 
    match derecurse_types tenv venv [ ("", [], t) ] with
    | ([ _, _, n ], venv) -> (n, venv)
    | _ -> assert false

let define_types (tenv, aenv) venv defs =
    let defs = List.map
        (fun (name, params, decl) -> (String.capitalize_ascii name, params, decl))
        defs
    in
    let (res, venv) = derecurse_types tenv venv defs in
    let tenv = List.fold_left
        (fun acc (name, params, typ) ->
            if params = [] then register name typ ;
            StrMap.add name (params, cons typ) acc)
        tenv
        res
    in ((tenv, aenv), venv)

let define_atom (env, atoms) name =
    let atom = String.uncapitalize_ascii name in
    let typ = String.capitalize_ascii name in
    if StrMap.mem typ env
    then raise (TypeDefinitionError (Printf.sprintf "Type %s already defined!" typ))
    else (StrMap.add typ ([], cons (mk_atom atom)) env, StrSet.add atom atoms)

let get_atom_type (env, _) name =
    let name = String.capitalize_ascii name in
    instantiate_alias env [] name

let has_atom (_, atoms) name =
    let name = String.uncapitalize_ascii name in
    StrSet.mem name atoms

(* Operations on types *)

module NHT = Hashtbl.Make(CD.Types.Node)

let conj ts = List.fold_left cap any ts
let disj ts = List.fold_left cup empty ts
let conj_o ts = List.fold_left cap_o any ts
let disj_o ts = List.fold_left cup_o empty ts

let is_test_type t =
    let is_non_trivial_arrow t =
        let arrow_part = cap t arrow_any in
        (is_empty arrow_part || subtype arrow_any arrow_part) |> not
    in
    let exception NotTestType in
    try
        let cache = NHT.create 5 in
        if vars t |> TVarSet.is_empty |> not then raise NotTestType ;
        let rec aux n =
            try NHT.find cache n
            with Not_found -> begin
                NHT.add cache n () ;
                let open Iter in
                iter (fun pack t ->
                    match pack with
                    | Absent | Abstract _ | Char _ | Int _ | Atom _ | Xml _ -> ()
                    | Times m ->
                        let module K = (val m) in
                        K.get_vars t |> K.Dnf.get_full |> List.iter (fun (_, (ps, ns)) ->
                            ps@ns |> List.iter (fun (a,b) -> aux a ; aux b)
                        )
                    | Function _ -> if is_non_trivial_arrow t then raise NotTestType
                    | Record m ->
                        let module K = (val m) in
                        K.get_vars t |> K.Dnf.get_full |> List.iter (fun (_, (ps, ns)) ->
                            ps@ns |> List.iter (fun (_,lm) -> LabelMap.iter aux lm)
                        )
                ) (descr n)
            end
        in aux (cons t) ; true
    with NotTestType -> false

let branch_type lst =
    if lst = [] then arrow_any
    else begin
        lst
        |> List.map (fun (a, b) -> mk_arrow (cons a) (cons b))
        |> conj
    end

let full_branch_type_aux line_typ ((pvs, nvs), (ps, ns)) =
    let pvs = pvs |> List.map TVar.typ |> conj in
    let nvs = nvs |> List.map TVar.typ |> List.map neg |> conj in
    let ps = ps |>
        List.map (fun l -> line_typ l) |> conj in
    let ns = ns |>
        List.map (fun l -> line_typ l |> neg) |> conj in
    [pvs;nvs;ps;ns] |> conj

let full_branch_type b =
    cap arrow_any (full_branch_type_aux (fun (a, b) -> mk_arrow a b) b)

let full_product_branch_type b =
    cap pair_any (full_branch_type_aux (fun (a, b) -> mk_times a b) b)

let full_record_branch_type b =
    cap record_any (full_branch_type_aux CD.Types.record_fields b)

(* Simplification of types *)

let regroup_conjuncts ~open_nodes conjuncts =
    let merge_conjuncts (l,r) (l',r') =
        if (NHT.mem open_nodes r |> not) && (NHT.mem open_nodes r' |> not)
            && equiv (descr l) (descr l')
        then Some (l, cap (descr r) (descr r') |> cons)
        else if (NHT.mem open_nodes l |> not) && (NHT.mem open_nodes l' |> not)
            && equiv (descr r) (descr r')
        then Some (cup (descr l) (descr l') |> cons, r)
        else None
    in
    Utils.merge_when_possible merge_conjuncts conjuncts

let regroup_conjuncts_descr ps =
    ps |>
    List.map (fun (a,b) -> (cons a, cons b)) |>
    regroup_conjuncts ~open_nodes:(NHT.create 0) |>
    List.map (fun (a,b) -> (descr a, descr b))

(* NOTE: regroup_disjuncts does not preserve equivalence but could be used
   sometimes to approximate a type with a larger and simpler one? *)
(* let regroup_disjuncts ~open_nodes disjuncts =
    let merge_disjuncts ((pvs,nvs), (ps,ns)) ((pvs',nvs'), (ps',ns')) =
        let (pvss, nvss, pvss', nvss') =
            (TVarSet.construct pvs, TVarSet.construct nvs,
            TVarSet.construct pvs', TVarSet.construct nvs') in
        if TVarSet.equal pvss pvss' && TVarSet.equal nvss nvss'
            && ns = [] && ns' = []
        then
            match ps, ps' with
            | [(l,r)], [(l',r')] ->
                if (NHT.mem open_nodes r |> not) && (NHT.mem open_nodes r' |> not)
                    && equiv (descr l) (descr l')
                then Some ((pvs,nvs), ([(l, cup (descr r) (descr r') |> cons)],[]))
                else if (NHT.mem open_nodes l |> not) && (NHT.mem open_nodes l' |> not)
                    && equiv (descr r) (descr r')
                then Some ((pvs,nvs), ([(cap (descr l) (descr l') |> cons, r)],[]))
                else None
            | _, _ -> None
        else None
    in
    Utils.merge_when_possible merge_disjuncts disjuncts *)

(* let regroup_disjuncts_simpl ds =
    ds |>
    List.map (fun ps ->
        let ps = ps |> List.map (fun (a,b) -> (cons a, cons b)) in
        (([], []), (ps,[]))
    ) |>
    regroup_disjuncts ~open_nodes:(NHT.create 0) |>
    List.map (fun (_,(ps,_)) ->
        ps |> List.map (fun (a,b) -> (descr a, descr b))
    ) *)

let simplify_dnf dnf =
    let simplify_conjuncts conjuncts =
        conjuncts |>
        List.map (fun (a, b) -> ((a,b), mk_arrow (cons a) (cons b))) |>
        Utils.filter_among_others (fun (_,t) ts -> subtype (List.map snd ts |> conj) t |> not)
        |> List.split |> fst |> regroup_conjuncts_descr
    in
    List.map (fun arrows -> (arrows, branch_type arrows)) dnf |>
    Utils.filter_among_others (fun (_,t) ts -> subtype t (List.map snd ts |> disj) |> not)
    |> List.map fst |> List.map simplify_conjuncts
    (* |> regroup_disjuncts_simpl *)

let remove_useless_conjuncts branch_type ~n dc cc lst =
    let atom_type (a,b) =
        if n then branch_type (([],[]),([],[(a,b)]))
        else branch_type (([],[]),([(a,b)],[]))
    in
    lst |> Utils.filter_among_others (fun c o ->
        let ct = atom_type c in
        let ot = o |> List.map atom_type |> conj in
        let ot = cap ot cc in
        let t  = cup dc (cap ot ct) in
        let t' = cup dc ot in
        subtype t' t |> not
    )

let remove_useless_conjuncts branch_type dc ((pvs, nvs), (ps, ns)) =
    let context = branch_type ((pvs, nvs), ([], ns)) in
    let ps = remove_useless_conjuncts branch_type ~n:false dc context ps in
    let context = branch_type ((pvs, nvs), (ps, [])) in
    let ns = remove_useless_conjuncts branch_type ~n:true dc context ns in
    ((pvs, nvs), (ps, ns))

let remove_useless_from_dnf branch_type dnf =
    (* Remove useless conjuncts *)
    dnf |> Utils.map_among_others (fun c others ->
        let ot = others |> List.map branch_type |> disj in
        remove_useless_conjuncts branch_type ot c
    ) |>
    (* Remove useless disjuncts *)
    Utils.filter_among_others (fun c others ->
        let ct = branch_type c in
        let ot = List.map branch_type others |> disj in
        subtype ct ot |> not
    )

let simplify_arrow_dnf ~open_nodes dnf =
    dnf |> remove_useless_from_dnf full_branch_type
    |> List.map
        (fun (vars, (ps, ns)) -> (vars, (regroup_conjuncts ~open_nodes ps, ns)))
    (* |> regroup_disjuncts ~open_nodes *)

let simplify_product_dnf ~open_nodes:_ dnf =
    (* TODO: More advanced simplifications for products *)
    dnf |> remove_useless_from_dnf full_product_branch_type

let simplify_record_dnf ~open_nodes:_ dnf =
    (* TODO: More advanced simplifications for records *)
    dnf |> remove_useless_from_dnf full_record_branch_type

let simplify_typ t =
    let cache = NHT.create 5 in
    let rec aux node =
        let aux_pair (a,b) = (aux a, aux b) in
        let aux_record (b, labelmap) = (b, LabelMap.map aux labelmap) in
        let aux_lines aux_line = List.map aux_line in
        let aux_branch aux_line ((pvs, nvs), (ps,ns)) =
            ((pvs,nvs),(aux_lines aux_line ps, aux_lines aux_line ns))
        in
        let aux_branches aux_line = List.map (aux_branch aux_line) in
        match NHT.find_opt cache node with
        | Some n -> n
        | None ->
            let n = mk_new_typ () in
            NHT.add cache node n ;
            let open Iter in
            let t = fold (fun acc pack t ->
                let t = match pack with
                | Absent -> absent
                | Abstract m | Char m | Int m | Atom m ->
                    let module K = (val m : Kind) in
                    K.get_vars t |> K.mk
                | Times m ->
                    let module K = (val m) in
                    K.get_vars t |> K.Dnf.get_full
                    |> simplify_product_dnf ~open_nodes:cache
                    |> aux_branches aux_pair
                    |> List.map full_product_branch_type |> disj
                | Xml m ->
                    let module K = (val m) in
                    K.get_vars t |> K.mk
                | Function m ->
                    let module K = (val m) in
                    K.get_vars t |> K.Dnf.get_full
                    |> simplify_arrow_dnf ~open_nodes:cache
                    |> aux_branches aux_pair
                    |> List.map full_branch_type |> disj
                | Record m ->
                    let module K = (val m) in
                    K.get_vars t |> K.Dnf.get_full
                    |> simplify_record_dnf ~open_nodes:cache
                    |> aux_branches aux_record
                    |> List.map full_record_branch_type |> disj
                in
                cup acc t
            ) empty (descr node) in
            define_typ n t ; n
    in
    let t' = aux (cons t) |> descr in
    assert (equiv t t') ; t'

(* Record manipulation *)

let record_any_with l = mk_record true [l, any_node]

let record_any_without l = mk_record true [l, (or_absent empty |> cons)]

let split_record t =
  let to_node (is_absent, t) =
    if is_absent
    then cons (CD.Types.Record.or_absent t)
    else cons t
  in
  let to_record (labels, is_open, _) =
    let labels = LabelMap.map to_node labels in
    CD.Types.record_fields (is_open, labels)
  in
  CD.Types.Record.get t |> List.map to_record

let remove_field_info t label =
    let t = remove_field t label in
    let singleton = mk_record false [label, any_or_absent_node] in
    merge_records t singleton

(* Operations on type variables *)

let apply_subst_simplify s t =
    if TVarSet.inter (Subst.dom s) (vars t) |> TVarSet.is_empty
    then t else Subst.apply s t |> simplify_typ

let instantiate ss t =
    List.map (fun s -> apply_subst_simplify s t) ss
    |> conj_o

let bot_instance =
    clean_type ~pos:empty ~neg:any

let top_instance =
    clean_type ~pos:any ~neg:empty    

let subtype_poly t1 t2 =
    let t2 = Subst.apply (monomorphize (vars t2)) t2 in
    tallying [(bot_instance t1,t2)] <> []
