open Cduce

module StrMap = Map.Make(String)
module StrSet = Set.Make(String)
module LabelMap = CD.Ident.LabelMap

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
    | TBase of type_base
    | TCustom of string
    | TPair of type_expr * type_expr
    | TRecord of bool * (string * type_expr * bool) list
    | TSList of type_regexp
    | TArrow of type_expr * type_expr
    | TCup of type_expr * type_expr
    | TCap of type_expr * type_expr
    | TDiff of type_expr * type_expr
    | TNeg of type_expr

type type_env = node StrMap.t * StrSet.t (* Atoms *)

let empty_tenv = (StrMap.empty, StrSet.empty)

let type_base_to_typ t =
    match t with
    | TInt (lb,ub) -> Cduce.interval lb ub
    | TSChar c -> Cduce.single_char c
    | TSString str -> Cduce.single_string str
    | TBool -> Cduce.bool_typ | TNil -> Cduce.nil_typ
    | TTrue -> Cduce.true_typ | TFalse -> Cduce.false_typ
    | TUnit -> Cduce.unit_typ | TChar -> Cduce.char_typ
    | TAny -> Cduce.any | TEmpty -> Cduce.empty
    | TString -> Cduce.string_typ | TList -> Cduce.list_typ

let derecurse_types env defs =
    let open Cduce_core in
    let henv = Hashtbl.create 16 in
    let () =
        List.iter (fun (name, def) ->
                if StrMap.mem name env then 
                    failwith (Printf.sprintf "Type %s already defined!" name)
                else
                    Hashtbl.add henv name (def, None)) defs
    in
    let rec get_name name =
        match Hashtbl.find henv name with
        | _, Some v -> v
        | def, None -> 
            let v = Typepat.mk_delayed () in
            Hashtbl.replace henv name (def, Some v);
            let t = aux def in
            Typepat.link v t;
            v
        | exception Not_found -> 
            try Typepat.mk_type (descr (StrMap.find name env))
            with Not_found -> 
                failwith (Printf.sprintf "Type %s undefined!" name)
    and aux t =
        match t with
        | TBase tb -> Typepat.mk_type (type_base_to_typ tb)
        | TCustom n -> get_name n
        | TPair (t1,t2) -> Typepat.mk_prod (aux t1) (aux t2)
        | TRecord (is_open, fields) ->
            let aux' (label,t,opt) =
                let n = aux t in
                let n = if opt then Typepat.mk_optional n else n in
                (Cduce.to_label label, (n, None))
            in
            let lmap = 
                Cduce_types.Ident.LabelMap.from_list_disj (List.map aux' fields)
            in
            Typepat.mk_record is_open lmap

        | TSList lst -> Typepat.rexp (aux_re lst)
        | TArrow (t1,t2) -> Typepat.mk_arrow (aux t1) (aux t2)
        | TCup (t1,t2) ->
            let t1 = aux t1 in
            let t2 = aux t2 in
            Typepat.mk_or t1 t2
        | TCap (t1,t2) ->
            let t1 = aux t1 in
            let t2 = aux t2 in
            Typepat.mk_and t1 t2
        | TDiff (t1,t2) ->
            let t1 = aux t1 in
            let t2 = aux t2 in
            Typepat.mk_diff t1 t2
        | TNeg t -> Typepat.mk_diff (Typepat.mk_type Cduce.any) (aux t)
    and aux_re r =
        match r with
        | ReEmpty -> Typepat.mk_empty
        | ReEpsilon -> Typepat.mk_epsilon
        | ReType t -> Typepat.mk_elem (aux t)
        | ReSeq (r1, r2) -> Typepat.mk_seq (aux_re r1) (aux_re r2)
        | ReAlt (r1, r2) -> Typepat.mk_alt (aux_re r1) (aux_re r2)
        | ReStar r -> Typepat.mk_star (aux_re r)
    in
    let nodes = List.map (fun (name, def) -> name, aux def) defs in
    List.map (fun (name, node) -> (name, 
                        (Typepat.internalize node; Typepat.typ node))) nodes


let type_expr_to_typ (tenv, _) t = 
    match derecurse_types tenv [ ("", t) ] with
    | [ _, n ] -> n
    | _ -> assert false

let define_types (tenv, aenv) defs =
    let defs = List.map
        (fun (name, decl) -> (String.capitalize_ascii name, decl))
        defs
    in
    let tenv = List.fold_left
        (fun acc (name, typ) ->
            Cduce.register name typ; 
            StrMap.add name (cons typ) acc)
        tenv
        (derecurse_types tenv defs)
    in (tenv, aenv)

let define_atom (env, atoms) name =
    let atom = String.uncapitalize_ascii name in
    let typ = String.capitalize_ascii name in
    if StrMap.mem typ env
    then failwith (Printf.sprintf "Type %s already defined!" typ)
    else (StrMap.add typ (cons (mk_atom atom)) env, StrSet.add atom atoms)


let get_type (env, _) name =
    let name = String.capitalize_ascii name in
    try descr (StrMap.find name env)
    with Not_found -> failwith (Printf.sprintf "Type %s undefined!" name)

let has_type (env, _) name =
    let name = String.capitalize_ascii name in
    StrMap.mem name env

let has_atom (_, atoms) name =
    let name = String.uncapitalize_ascii name in
    StrSet.mem name atoms

(* Operations on types *)

let conj ts = List.fold_left cap_o any ts
let disj ts = List.fold_left cup_o empty ts

let apply_opt t s =
    if subtype s (domain t) then apply t s else any

let branch_type lst =
    if lst = [] then arrow_any
    else begin
        lst
        |> List.map (fun (a, b) -> mk_arrow (cons a) (cons b))
        |> conj
    end

let rec take_one lst =
    match lst with
    | [] -> []
    | e::lst ->
        (e, lst)::(List.map (fun (e',lst) -> (e',e::lst)) (take_one lst))

let simplify_dnf dnf =
    let splits = List.map branch_type dnf in
    let splits = List.combine dnf splits in
    let rec rm f kept lst = match lst with
    | [] -> kept
    | (dnf, t)::lst ->
        let (_, ts1) = List.split lst in
        let (_, ts2) = List.split kept in
        if f t (ts1@ts2) then rm f kept lst else rm f ((dnf, t)::kept) lst
    in
    let rec regroup conjuncts =
        let rec aux (l,r) lst = match lst with
        | [] -> ((l,r), [])
        | (l',r')::lst ->
            if equiv l l'
            then aux (l, cap_o r r') lst
            else if equiv r r'
            then aux (cup_o l l', r) lst
            else
                let ((l,r),lst) = aux (l,r) lst in
                ((l,r), (l',r')::lst)
        in
        match conjuncts with
        | [] -> []
        | (l, r)::lst ->
            let ((l,r),lst) = aux (l,r) lst in
            (l,r)::(regroup lst)
    in
    let simplify_conjuncts (conjuncts, _) =
        let conjuncts = conjuncts |>
            List.map (fun (a, b) -> ((a,b), mk_arrow (cons a) (cons b))) |>
            rm (fun t ts -> subtype (conj ts) t) [] (* Remove redundant conjuncts *)
        in
        conjuncts |> List.split |> fst |> regroup (* Regroup conjuncts with similar domain/codomain *)
    in
    rm (fun t ts -> subtype t (disj ts)) [] splits
    |> List.map simplify_conjuncts

let simplify_arrow t = (* Warning: only keep the positive part *)
    let res = dnf t |> simplify_dnf |> List.map branch_type |> disj in
    assert (equiv res (dnf t |> List.map branch_type |> disj)) ; res

let simplify_typ t = (* Warning: only keep the positive part of functions *)
    let arrow = cap_o t arrow_any |> simplify_arrow in
    let non_arrow = diff t arrow_any |> normalize_typ in
    cup_o arrow non_arrow
    
let split_arrow t =
  dnf t
  |> List.map branch_type

let is_test_type t =
    let is_non_trivial_arrow t =
        let arrow_part = cap_o t arrow_any in
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
    in
    aux t

let square_approx f out =
    let res = dnf f |> List.map begin
        fun lst ->
            let is_impossible (_,t) = is_empty (cap_o out t) in
            let impossibles = List.filter is_impossible lst |> List.map fst in
            neg (disj impossibles)
    end in
    cap_o (domain f) (disj res)

let square_exact f out =
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
    cap_o (domain f) (disj res)

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
            let remove_disjoint_branchs lst =
                let is_not_disjoint (_, o) = disjoint o out |> not in
                List.filter is_not_disjoint lst
            in
            let rec possible_inputs current_set lst =
                let t = List.map snd current_set in
                if subtype (conj t) out then [conj (List.map fst current_set)]
                else begin
                    let aux (e,lst) = possible_inputs (e::current_set) lst in
                    List.flatten (List.map aux (take_one lst))
                end
            in
            disj (possible_inputs [] (remove_disjoint_branchs lst))
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
