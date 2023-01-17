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
    | TString | TList

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

let conj ts = List.fold_left cap any ts
let disj ts = List.fold_left cup empty ts
let conj_o ts = List.fold_left cap_o any ts
let disj_o ts = List.fold_left cup_o empty ts

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

let rec take_one lst =
    match lst with
    | [] -> []
    | e::lst ->
        (e, lst)::(List.map (fun (e',lst) -> (e',e::lst)) (take_one lst))

module NHT = Hashtbl.Make(CD.Types.Node)
let rec regroup_conjuncts ~open_nodes conjuncts =
    let rec aux (l,r) lst = match lst with
    | [] -> ((l,r), [])
    | (l',r')::lst ->
        if (NHT.mem open_nodes r |> not) && (NHT.mem open_nodes r' |> not)
            && equiv (descr l) (descr l')
        then aux (l, cap (descr r) (descr r') |> cons) lst
        else if (NHT.mem open_nodes l |> not) && (NHT.mem open_nodes l' |> not)
            && equiv (descr r) (descr r')
        then aux (cup (descr l) (descr l') |> cons, r) lst
        else
            let ((l,r),lst) = aux (l,r) lst in
            ((l,r), (l',r')::lst)
    in
    match conjuncts with
    | [] -> []
    | (l, r)::lst ->
        let ((l,r),lst) = aux (l,r) lst in
        (l,r)::(regroup_conjuncts ~open_nodes lst)

let regroup_conjuncts_descr ps =
    ps |>
    List.map (fun (a,b) -> (cons a, cons b)) |>
    regroup_conjuncts ~open_nodes:(NHT.create 0) |>
    List.map (fun (a,b) -> (descr a, descr b))

let simplify_dnf dnf =
    let splits = List.map (fun arrows -> (arrows, branch_type arrows)) dnf in
    let rec rm f kept lst = match lst with
    | [] -> kept
    | (dnf, t)::lst ->
        let (_, ts1) = List.split lst in
        let (_, ts2) = List.split kept in
        if f t (ts1@ts2) then rm f kept lst else rm f ((dnf, t)::kept) lst
    in
    let simplify_conjuncts (conjuncts, _) =
        let conjuncts = conjuncts |>
            List.map (fun (a, b) -> ((a,b), mk_arrow (cons a) (cons b))) |>
            rm (fun t ts -> subtype (conj ts) t) [] (* Remove redundant conjuncts *)
        in
        (* Regroup conjuncts with similar domain/codomain *)
        conjuncts |> List.split |> fst |> regroup_conjuncts_descr
    in
    rm (fun t ts -> subtype t (disj ts)) [] splits
    |> List.map simplify_conjuncts        

let remove_useless_conjuncts branch_type ~n dc cc lst =
    let atom_type (a,b) =
        if n then branch_type (([],[]),([],[(a,b)]))
        else branch_type (([],[]),([(a,b)],[]))
    in
    let rec aux kept rem =
        match rem with
        | [] -> kept
        | c::rem ->
            let ct = atom_type c in
            let rt = rem |> List.map atom_type |> conj in
            let kt = kept |> List.map atom_type |> conj in
            let others = conj [kt ; rt ; cc] in
            let t' = cup dc others in
            let t  = cup dc (cap others ct) in
            if subtype t' t then aux kept rem
            else aux (c::kept) rem
    in
    aux [] lst

let remove_useless_conjuncts branch_type dc ((pvs, nvs), (ps, ns)) =
    let context = branch_type ((pvs, nvs), ([], ns)) in
    let ps = remove_useless_conjuncts branch_type ~n:false dc context ps in
    let context = branch_type ((pvs, nvs), (ps, [])) in
    let ns = remove_useless_conjuncts branch_type ~n:true dc context ns in
    ((pvs, nvs), (ps, ns))

let remove_useless_from_dnf branch_type dnf =
    (* Remove useless conjuncts *)
    let rec aux treated rem =
        match rem with
        | [] -> treated
        | c::rem ->
            let rt = rem |> List.map branch_type |> disj in
            let tt = treated |> List.map branch_type |> disj in
            let others = cup tt rt in
            let c = remove_useless_conjuncts branch_type others c in
            aux (c::treated) rem
    in
    let dnf = aux [] dnf in
    (* Remove useless disjuncts *)
    let rec aux kept rem =
        match rem with
        | [] -> kept
        | c::rem ->
            let ct = branch_type c in
            let rt = rem |> List.map branch_type |> disj in
            let kt = kept |> List.map branch_type |> disj in
            let others = cup kt rt in
            if subtype ct others then aux kept rem
            else aux (c::kept) rem
    in
    aux [] dnf

let simplify_arrow_dnf ~open_nodes dnf =
    let regroup_conjuncts (vars, (ps, ns)) =
        (vars, (regroup_conjuncts ~open_nodes ps, ns))
    in
    let dnf = remove_useless_from_dnf full_branch_type dnf in
    (* Regroup positive conjuncts with similar domain/codomain  *)
    List.map regroup_conjuncts dnf

let simplify_product_dnf ~open_nodes:_ dnf =
    let dnf = remove_useless_from_dnf full_product_branch_type dnf in
    (* TODO: More advanced simplifications for products *)
    dnf

let simplify_record_dnf ~open_nodes:_ dnf =
    let dnf = remove_useless_from_dnf full_record_branch_type dnf in
    (* TODO: More advanced simplifications for records *)
    dnf

let is_test_type t =
    if vars t |> TVarSet.is_empty
    then
        let is_non_trivial_arrow t =
            let arrow_part = cap t arrow_any in
            (is_empty arrow_part || subtype arrow_any arrow_part) |> not
        in
        let memo = Hashtbl.create 10 in
        let rec aux t =
            try Hashtbl.find memo t
            with Not_found -> begin
                if is_non_trivial_arrow t
                then (Hashtbl.add memo t false ; false)
                else begin
                    Hashtbl.add memo t true ;
                    split_pair t |>
                    List.for_all (fun (x,y) -> aux x && aux y)
                end
            end
        in aux t
    else false

let simplify_typ t =
    (*Utils.log ~level:2 "Simplifying type...@?" ;*)
    let cache = NHT.create 5 in
    let rec aux node =
        let aux_pair (a,b) = (aux a, aux b) in
        let aux_record (b, labelmap) = (b, LabelMap.map aux labelmap) in
        let aux_lines aux_line ls =
            ls |> List.map aux_line
        in
        let aux_branch aux_line ((pvs, nvs), (ps,ns)) =
            ((pvs,nvs),(aux_lines aux_line ps, aux_lines aux_line ns))
        in
        let aux_branches aux_line lst =
            lst |> List.map (fun branch -> aux_branch aux_line branch)
        in
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
    aux (cons t) |> descr

let square_approx f out =
    let res = dnf f |> List.map begin
        fun lst ->
            let is_impossible (_,t) = is_empty (cap out t) in
            let impossibles = List.filter is_impossible lst |> List.map fst in
            neg (disj impossibles)
    end in
    cap (domain f) (disj res)

let square_exact f out =
    assert (is_empty out |> not) ;
    let res = dnf f |> List.map begin
        fun lst ->
            let remove_included_branchs lst =
                let is_not_included (_, o) = subtype o out |> not in
                List.filter is_not_included lst
            in
            let rec impossible_inputs current_set lst =
                let t = List.map snd current_set in
                if disjoint (conj t) out then [conj (List.map fst current_set)]
                else begin
                    let aux (e,lst) = impossible_inputs (e::current_set) lst in
                    List.flatten (List.map aux (take_one lst))
                end
            in
            conj (List.map neg (impossible_inputs [] (remove_included_branchs lst)))
    end in
    cap (domain f) (disj res)

let square_split f out =
    dnf f |>
    List.map begin
        fun lst ->
            let t = branch_type lst in
            let res = square_exact t out in
            (t, res)
    end

let triangle_exact f out =
    let res = dnf f |> List.map begin
        fun lst ->
            (*let remove_disjoint_branchs lst =
                let is_not_disjoint (_, o) = disjoint o out |> not in
                List.filter is_not_disjoint lst
            in*)
            let rec possible_inputs current_set lst =
                let t = List.map snd current_set in
                if t <> [] && subtype (conj t) out then [conj (List.map fst current_set)]
                else begin
                    let aux (e,lst) = possible_inputs (e::current_set) lst in
                    List.flatten (List.map aux (take_one lst))
                end
            in
            disj (possible_inputs [] ((*remove_disjoint_branchs*)lst))
    end in
    conj res

let triangle_split f out =
    dnf f |>
    List.map begin
        fun lst ->
            let t = branch_type lst in
            let res = triangle_exact t out in
            (t, res)
    end

(* Record manipulation *)
let record_any_with l = mk_record true [l, any_node]

let record_any_without l = mk_record true [l, (or_absent empty |> cons)]

let split_record t =
  let to_node (is_absent, t) =
    if is_absent then
      cons (CD.Types.Record.or_absent t)
    else
      cons t
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

(* Operations on type vars *)
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
