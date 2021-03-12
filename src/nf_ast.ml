open Variable
module ExprMap = Ast.ExprMap

type a =
  | Abstract of Cduce.typ
  | Const of Ast.const
  | Lambda of (Cduce.typ Ast.type_annot) * Variable.t * e
  | Ite of Variable.t * Cduce.typ * Variable.t * Variable.t
  | App of Variable.t * Variable.t
  | Pair of Variable.t * Variable.t
  | Projection of Ast.projection * Variable.t
  | RecordUpdate of Variable.t * string * Variable.t option
  | Let of Variable.t * Variable.t
  | Debug of string * Variable.t
  [@@deriving show]

and e =
  | Bind of Variable.t * a * e
  | Var of Variable.t
  [@@deriving show]


let map ef af =
  let rec aux_a a =
    begin match a with
    | Abstract t -> Abstract t
    | Const c -> Const c
    | Lambda (ta, v, e) -> Lambda (ta, v, aux_e e)
    | Ite (v, t, x1, x2) -> Ite (v, t, x1, x2)
    | App (v1, v2) -> App (v1, v2)
    | Pair (v1, v2) -> Pair (v1, v2)
    | Projection (p, v) -> Projection (p, v)
    | RecordUpdate (v, str, vo) -> RecordUpdate (v, str, vo)
    | Let (v1, v2) -> Let (v1, v2)
    | Debug (str, v) -> Debug (str, v)
    end
    |> af
  and aux_e e =
    begin match e with
    | Bind (v, a, e) -> Bind (v, aux_a a, aux_e e)
    | Var v -> Var v
    end
    |> ef
  in (aux_e, aux_a)

let map_e ef af = map ef af |> fst
let map_a ef af = map ef af |> snd

let fold ef af =
  let rec aux_a a =
    begin match a with
    | Abstract _ | Const _ | Debug _ | App _ | Pair _
    | Projection _ | RecordUpdate _ | Ite _ | Let _ -> []
    | Lambda (_, _, e) -> [aux_e e]
    end
    |> af a
  and aux_e e =
    begin match e with
    | Bind (_, a, e) -> [aux_a a ; aux_e e]
    | Var _ -> []
    end
    |> ef e
  in (aux_e, aux_a)

let fold_e ef af = fold ef af |> fst
let fold_a ef af = fold ef af |> snd


let free_vars =
  let f1 e acc =
    let acc = List.fold_left VarSet.union VarSet.empty acc in
    match e with
    | Bind (v, _, _) -> VarSet.remove v acc
    | Var v -> VarSet.add v acc
  in
  let f2 a acc =
    let acc = List.fold_left VarSet.union VarSet.empty acc in
    match a with
    | Lambda (_, v, _) -> VarSet.remove v acc
    | Projection (_, v) | Debug (_, v) | RecordUpdate (v, _, None) ->
      VarSet.add v acc
    | Ite (v, _, x1, x2) -> VarSet.add v acc |> VarSet.add x1 |> VarSet.add x2
    | App (v1, v2) | Pair (v1, v2) | Let (v1, v2) | RecordUpdate (v1, _, Some v2) ->
      VarSet.add v1 acc |> VarSet.add v2
    | Const _ | Abstract _ -> acc
  in
  (fold_a f1 f2, fold_e f1 f2)

let fv_a = free_vars |> fst
let fv_e = free_vars |> snd

let bound_vars =
  let f1 e acc =
    let acc = List.fold_left VarSet.union VarSet.empty acc in
    match e with Bind (v, _, _) -> VarSet.add v acc | Var _ -> acc
  in
  let f2 a acc =
    let acc = List.fold_left VarSet.union VarSet.empty acc in
    match a with Lambda (_, v, _) -> VarSet.add v acc | _ -> acc
  in
  (fold_a f1 f2, fold_e f1 f2)

let bv_a = bound_vars |> fst
let bv_e = bound_vars |> snd

let rec separate_defs bvs defs =
  match defs with
  | [] -> ([], [])
  | (v,d)::defs ->
    let fvs = fv_a d in
    if VarSet.inter bvs fvs |> VarSet.is_empty
    then
      let (defs, defs') = separate_defs bvs defs in
      ((v,d)::defs, defs')
    else
      let bvs = VarSet.add v bvs in
      let (defs, defs') = separate_defs bvs defs in
      (defs, (v,d)::defs')

let extract_from_expr_map vals em =
  ExprMap.bindings em |>
  List.filter (fun (_, v) -> VarSet.mem v vals) |>
  List.fold_left (fun (acc1,acc2) (e,v) ->
    (ExprMap.add e v acc1, ExprMap.remove e acc2)
  )
  (ExprMap.empty, em)

exception IsVar of Variable.t

let convert_to_normal_form ast =
  let aux expr_var_map ast =
    let rec to_defs_and_a expr_var_map ast =
      let (_, e) = ast in
      let uast = Ast.unannot_and_normalize ast in
      if ExprMap.mem uast expr_var_map
      then raise (IsVar (ExprMap.find uast expr_var_map))
      else match e with
      | Ast.Abstract t -> ([], expr_var_map, Abstract t)
      | Ast.Const c -> ([], expr_var_map, Const c)
      | Ast.Var v -> raise (IsVar v)
      | Ast.Lambda (t, v, e) ->
        (*let e = aux expr_var_map e in
        ([], expr_var_map, Lambda (t, v, e))*)
        (* We try to factorize as much as possible *)
        let (defs', expr_var_map', x) = to_defs_and_x expr_var_map e in
        let (defs, defs') =
          List.rev defs' |>
          separate_defs (VarSet.singleton v) in
        let (expr_var_map, _) = expr_var_map' |>
          extract_from_expr_map (defs |> List.map fst |> VarSet.of_list) in
        let (defs, defs') = (List.rev defs, List.rev defs') in
        let e = defs_and_x_to_e defs' x in
        (defs, expr_var_map, Lambda (t, v, e))
      | Ast.Ite (e, t, e1, e2) ->
        let (defs, expr_var_map, x) = to_defs_and_x expr_var_map e in
        let (defs1, expr_var_map, x1) = to_defs_and_x expr_var_map e1 in
        let (defs2, expr_var_map, x2) = to_defs_and_x expr_var_map e2 in
        (defs2@defs1@defs, expr_var_map, Ite (x, t, x1, x2))
      | Ast.Let (v, e1, e2) ->
        let name = Variable.get_name v in
        let (defs1, expr_var_map, x) = to_defs_and_x ~name expr_var_map e1 in
        let e2 = Ast.substitute e2 v e1 in (* Substitute v by e1 in e2 *)
        let (defs2, expr_var_map, y) = to_defs_and_x expr_var_map e2 in
        (defs2@defs1, expr_var_map, Let (x, y))
      | Ast.App (e1, e2) ->
        let (defs1, expr_var_map, x1) = to_defs_and_x expr_var_map e1 in
        let (defs2, expr_var_map, x2) = to_defs_and_x expr_var_map e2 in
        (defs2@defs1, expr_var_map, App (x1, x2))
      | Ast.Pair (e1, e2) ->
        let (defs1, expr_var_map, x1) = to_defs_and_x expr_var_map e1 in
        let (defs2, expr_var_map, x2) = to_defs_and_x expr_var_map e2 in
        (defs2@defs1, expr_var_map, Pair (x1, x2))
      | Ast.Projection (p, e) ->
        let (defs, expr_var_map, x) = to_defs_and_x expr_var_map e in
        (defs, expr_var_map, Projection (p, x))
      | Ast.RecordUpdate (e, str, None) ->
        let (defs, expr_var_map, x) = to_defs_and_x expr_var_map e in
        (defs, expr_var_map, RecordUpdate (x, str, None))
      | Ast.RecordUpdate (e, str, Some e') ->
        let (defs, expr_var_map, x) = to_defs_and_x expr_var_map e in
        let (defs', expr_var_map, x') = to_defs_and_x expr_var_map e' in
        (defs'@defs, expr_var_map, RecordUpdate (x, str, Some x'))
      | Ast.Debug (str, e) ->
        let (defs, expr_var_map, x) = to_defs_and_x expr_var_map e in
        (defs, expr_var_map, Debug (str, x))

    and to_defs_and_x ?(name=None) expr_var_map ast =
      let ((_, pos), _) = ast in
      try
        let (defs, expr_var_map, a) = to_defs_and_a expr_var_map ast in
        let var = Variable.create name in
        Variable.attach_location var pos ;
        let expr_var_map =
          ExprMap.add (Ast.unannot_and_normalize ast) var expr_var_map in
        let defs = (var, a)::defs in
        (defs, expr_var_map, var)
      with IsVar v ->
        (Variable.attach_location v pos ; ([], expr_var_map, v))
    
    and defs_and_x_to_e defs x =
      defs |>
      List.fold_left (
        fun nf (v, d) ->
        Bind (v, d, nf)
      ) (Var x)
    in
    
    let (defs, _, x) = to_defs_and_x expr_var_map ast in
    defs_and_x_to_e defs x

  in aux ExprMap.empty ast

let convert_a_to_e a pos =
  let var = Variable.create None in
  List.iter (fun pos -> Variable.attach_location var pos) pos ;
  Bind (var, a, Var var)
