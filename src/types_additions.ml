open Cduce

module StrMap = Map.Make(String)

(* Construction of types *)

type type_base =
    TInt of int option * int option
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
                let t = descr (aux t) in
                (label, cons (if opt then or_absent t else t))
            in
            let fields = List.map aux' fields in
            cons (mk_record is_open fields)
        | TArrow (t1,t2) -> cons (mk_arrow (aux t1) (aux t2))
        | TCup (t1,t2) ->
            let t1 = descr (aux t1) in
            let t2 = descr (aux t2) in
            cons (cup t1 t2)
        | TCap (t1,t2) ->
            let t1 = descr (aux t1) in
            let t2 = descr (aux t2) in
            cons (cap t1 t2)
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
        define_typ (StrMap.find name env) t
    in
    List.iter define_type defs ; env

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
    lst
    |> List.map (fun (a, b) -> mk_arrow (cons a) (cons b))
    |> conj

let rec take_one lst =
    match lst with
    | [] -> []
    | e::lst ->
        (e, lst)::(List.map (fun (e',lst) -> (e',e::lst)) (take_one lst))

let simplify_dnf dnf =
    let splits = List.map branch_type dnf in
    let splits = List.combine dnf splits in
    let rec aux f kept lst = match lst with
    | [] -> kept
    | (dnf, t)::lst ->
        let (_, ts1) = List.split lst in
        let (_, ts2) = List.split kept in
        if f t (ts1@ts2) then aux f kept lst else aux f ((dnf, t)::kept) lst
    in
    let simplify_conjuncts (conjuncts, _) =
        let conjuncts = List.map (fun (a, b) -> ((a,b), mk_arrow (cons a) (cons b))) conjuncts in
        aux (fun t ts -> subtype (conj ts) t) [] conjuncts
        |> List.split |> fst (* TODO: regroup conjuncts when similar domain/codomain *)
    in
    aux (fun t ts -> subtype t (disj ts)) [] splits
    |> List.map simplify_conjuncts

let simplify_arrow t =
    dnf t |> simplify_dnf
    |> List.map branch_type |> disj
    
let split_arrow t =
  dnf t
  |> List.map branch_type

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
