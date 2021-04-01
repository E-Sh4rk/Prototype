open Cduce

module StrMap = Map.Make(String)
module LabelMap = CD.Ident.LabelMap

(* Construction of types *)

type type_base =
    | TInt of int option * int option | TSChar of char
    | TBool | TTrue | TFalse | TUnit | TChar | TAny | TEmpty

type type_expr =
| TBase of type_base
| TCustom of string
| TPair of type_expr * type_expr
| TRecord of bool * (string * type_expr * bool) list
| TArrow of type_expr * type_expr
| TCup of type_expr * type_expr
| TCap of type_expr * type_expr
| TDiff of type_expr * type_expr
| TNeg of type_expr

type type_env = node StrMap.t

let empty_tenv = StrMap.empty

let type_base_to_typ t =
    match t with
    | TInt (lb,ub) -> Cduce.interval lb ub
    | TSChar c -> Cduce.single_char c
    | TBool -> Cduce.bool_typ
    | TTrue -> Cduce.true_typ | TFalse -> Cduce.false_typ
    | TUnit -> Cduce.unit_typ | TChar -> Cduce.char_typ
    | TAny -> Cduce.any | TEmpty -> Cduce.empty

let type_expr_to_typ env t =
    let rec aux t =
        match t with
        | TBase tb -> cons (type_base_to_typ tb)
        | TCustom k ->
            (try StrMap.find k env with Not_found -> failwith (Printf.sprintf "Type %s undefined!" k))
        | TPair (t1,t2) -> cons (mk_times (aux t1) (aux t2))
        | TRecord (is_open, fields) ->
            let aux' (label,t,opt) =
                let n = aux t in
                let () = if opt then
                       let ndef = or_absent (descr n) in
                       define_typ n ndef
                       in
                (label,  n)
            in
            let fields = List.map aux' fields in
            cons (mk_record is_open fields)
        | TArrow (t1,t2) -> cons (mk_arrow (aux t1) (aux t2))
        | TCup (t1,t2) ->
            let t1 = descr (aux t1) in
            let t2 = descr (aux t2) in
            cons (cup_r t1 t2)
        | TCap (t1,t2) ->
            let t1 = descr (aux t1) in
            let t2 = descr (aux t2) in
            cons (cap_r t1 t2)
        | TDiff (t1,t2) ->
            let t1 = descr (aux t1) in
            let t2 = descr (aux t2) in
            cons (diff t1 t2)
        | TNeg t -> cons (neg (descr (aux t)))
    in descr (aux t)

let define_atom env atom =
    let atom = String.capitalize_ascii atom in
    if StrMap.mem atom env
    then failwith (Printf.sprintf "Atom %s already defined!" atom)
    else StrMap.add atom (cons (mk_atom atom)) env

let define_types env defs =
    let declare_type env (name,_) =
        let name = String.capitalize_ascii name in
        if StrMap.mem name env
        then failwith (Printf.sprintf "Type %s already defined!" name)
        else StrMap.add name (mk_new_typ ()) env
    in
    let env = List.fold_left declare_type env defs in
    let define_type (name,decl) =
        let name = String.capitalize_ascii name in
        let t = type_expr_to_typ env decl in
        let x = StrMap.find name env in
        let t = if has_absent (descr x) then or_absent t else t in
        define_typ x t;
    in
    List.iter define_type defs ;
    (* fix top-level optional types *)
    StrMap.fold (fun name node acc ->
                let t = descr node in
                let nnode =
                    if has_absent t then cons (diff t absent) else node
                in
                StrMap.add name nnode acc) env StrMap.empty

let get_type_or_atom env name =
    let name = String.capitalize_ascii name in
    try descr (StrMap.find name env)
    with Not_found -> failwith (Printf.sprintf "Type %s undefined!" name)

let has_type_or_atom env name =
    let name = String.capitalize_ascii name in
    StrMap.mem name env

(* Operations on types *)

let conj ts = List.fold_left cap any ts
let disj ts = List.fold_left cup empty ts

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
            then aux (l, cap r r') lst
            else if equiv r r'
            then aux (cup l l', r) lst
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

let simplify_arrow t =
    let res = dnf t |> simplify_dnf |> List.map branch_type |> disj in
    assert (equiv res t) ; res

let simplify_typ t =
    let arrow = cap t arrow_any |> simplify_arrow in
    let non_arrow = diff t arrow_any |> normalize_typ in
    cup arrow non_arrow
    
let split_arrow t =
  dnf t
  |> List.map branch_type

let is_test_type t =
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
    in
    aux t

let square_approx f out =
    let res = dnf f |> List.map begin
        fun lst ->
            let is_impossible (_,t) = is_empty (cap out t) in
            let impossibles = List.filter is_impossible lst |> List.map fst in
            neg (disj impossibles)
    end in
    cap (domain f) (disj res)

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
    (*let label = CD.Ident.Label.mk_ascii label in
    let to_filtered_node l (is_absent, t) =
        if CD.Ident.Label.equal label l
        then any_or_absent_node
        else if is_absent
        then cons (CD.Types.Record.or_absent t)
        else cons t
    in
    let to_filtered_record (labels, is_open, _) =
        let labels = LabelMap.mapi to_filtered_node labels in
        CD.Types.record_fields (is_open, labels)
    in
    CD.Types.Record.get t |> List.map to_filtered_record |> disj*)
    let t = remove_field t label in
    let singleton = mk_record false [label, any_or_absent_node] in
    merge_records t singleton
