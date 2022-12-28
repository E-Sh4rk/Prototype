open Parsing
open Parsing.Variable
module ExprMap = Parsing.Ast.ExprMap
open Types.Base

type 'va a =
  | Alias of Variable.t
  | Abstract of typ
  | Const of Ast.const
  | Lambda of 'va * (typ Ast.type_annot) * Variable.t * 'va e
  | Ite of Variable.t * typ * Variable.t * Variable.t
  | App of Variable.t * Variable.t
  | Pair of Variable.t * Variable.t
  | Projection of Ast.projection * Variable.t
  | RecordUpdate of Variable.t * string * Variable.t option
  | Let of Variable.t * Variable.t
  | TypeConstr of Variable.t * typ
  [@@deriving show]

and 'va e =
  | Bind of 'va * Variable.t * 'va a * 'va e
  | Var of Variable.t
  [@@deriving show]

let map ef af =
  let rec aux_a a =
    begin match a with
    | Alias v -> Alias v
    | Abstract t -> Abstract t
    | Const c -> Const c
    | Lambda (va, ta, v, e) -> Lambda (va, ta, v, aux_e e)
    | Ite (v, t, x1, x2) -> Ite (v, t, x1, x2)
    | App (v1, v2) -> App (v1, v2)
    | Pair (v1, v2) -> Pair (v1, v2)
    | Projection (p, v) -> Projection (p, v)
    | RecordUpdate (v, str, vo) -> RecordUpdate (v, str, vo)
    | Let (v1, v2) -> Let (v1, v2)
    | TypeConstr (v, t) -> TypeConstr (v, t)
    end
    |> af
  and aux_e e =
    begin match e with
    | Bind (va, v, a, e) -> Bind (va, v, aux_a a, aux_e e)
    | Var v -> Var v
    end
    |> ef
  in (aux_e, aux_a)

let map_e ef af = map ef af |> fst
let map_a ef af = map ef af |> snd

let rec map_annot_a ef af a =
  match a with
    | Alias v -> Alias v
    | Abstract t -> Abstract t
    | Const c -> Const c
    | Lambda (va, ta, v, e) -> Lambda (af va, ta, v, map_annot_e ef af e)
    | Ite (v, t, x1, x2) -> Ite (v, t, x1, x2)
    | App (v1, v2) -> App (v1, v2)
    | Pair (v1, v2) -> Pair (v1, v2)
    | Projection (p, v) -> Projection (p, v)
    | RecordUpdate (v, str, vo) -> RecordUpdate (v, str, vo)
    | Let (v1, v2) -> Let (v1, v2)
    | TypeConstr (v, t) -> TypeConstr (v, t)
and map_annot_e ef af e =
    match e with
    | Bind (va, v, a, e) -> Bind (ef va, v, map_annot_a ef af a, map_annot_e ef af e)
    | Var v -> Var v

let fold ef af =
  let rec aux_a a =
    begin match a with
    | Alias _ | Abstract _ | Const _ | App _ | Pair _
    | Projection _ | RecordUpdate _ | Ite _ | Let _
    | TypeConstr _ -> []
    | Lambda (_, _, _, e) -> [aux_e e]
    end
    |> af a
  and aux_e e =
    begin match e with
    | Bind (_, _, a, e) -> [aux_a a ; aux_e e]
    | Var _ -> []
    end
    |> ef e
  in (aux_e, aux_a)

let fold_e ef af = fold ef af |> fst
let fold_a ef af = fold ef af |> snd

let fv_e' e acc =
  let acc = List.fold_left VarSet.union VarSet.empty acc in
  match e with
  | Bind (_, v, _, _) -> VarSet.remove v acc
  | Var v -> VarSet.add v acc
let fv_a' a acc =
  let acc = List.fold_left VarSet.union VarSet.empty acc in
  match a with
  | Lambda (_, _, v, _) -> VarSet.remove v acc
  | Alias v | Projection (_, v) | RecordUpdate (v, _, None)
  | TypeConstr (v, _) -> VarSet.add v acc
  | Ite (v, _, x1, x2) -> VarSet.add v acc |> VarSet.add x1 |> VarSet.add x2
  | App (v1, v2) | Pair (v1, v2) | Let (v1, v2) | RecordUpdate (v1, _, Some v2) ->
    VarSet.add v1 acc |> VarSet.add v2
  | Const _ | Abstract _ -> acc

let fv_a x = fold_a fv_e' fv_a' x
let fv_e x = fold_e fv_e' fv_a' x

let bv_e' e acc =
  let acc = List.fold_left VarSet.union VarSet.empty acc in
  match e with Bind (_, v, _, _) -> VarSet.add v acc | Var _ -> acc
let bv_a' a acc =
  let acc = List.fold_left VarSet.union VarSet.empty acc in
  match a with Lambda (_, _, v, _) -> VarSet.add v acc | _ -> acc

let bv_a x = fold_a bv_e' bv_a' x
let bv_e x = fold_e bv_e' bv_a' x

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

let filter_expr_map vals em =
  ExprMap.filter (fun _ node ->
    let v = ExprMap.get_el node in
    VarSet.mem v vals
  ) em

exception IsVar of Variable.t

let convert_to_msc ast =
  let aux expr_var_map ast =
    let rec to_defs_and_a expr_var_map ast =
      let (_, e) = ast in
      let uast = Ast.unannot_and_normalize ast in
      if ExprMap.mem uast expr_var_map
      then
        let (_,node) = ExprMap.find uast expr_var_map in
        raise (IsVar (ExprMap.get_el node))
      else match e with
      | Ast.Abstract t -> ([], expr_var_map, Abstract t)
      | Ast.Const c -> ([], expr_var_map, Const c)
      | Ast.Var v when Variable.is_binding_var v -> raise (IsVar v)
      | Ast.Var v -> ([], expr_var_map, Alias v)
      | Ast.Lambda (t, v, e) ->
        (*let e = aux expr_var_map e in
        ([], expr_var_map, Lambda (t, v, e))*)
        (* We try to factorize as much as possible *)
        let (defs', expr_var_map', x) = to_defs_and_x expr_var_map e in
        let (defs, defs') =
          List.rev defs' |>
          separate_defs (VarSet.singleton v) in
        let expr_var_map = expr_var_map' |>
          filter_expr_map (defs |> List.map fst |> VarSet.of_list) in
        let (defs, defs') = (List.rev defs, List.rev defs') in
        let e = defs_and_x_to_e defs' x in
        (defs, expr_var_map, Lambda ((), t, v, e))
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
      | Ast.TypeConstr (e, t) ->
        let (defs, expr_var_map, x) = to_defs_and_x expr_var_map e in
        (defs, expr_var_map, TypeConstr (x, t))

    and to_defs_and_x ?(name=None) expr_var_map ast =
      let ((_, pos), _) = ast in
      try
        let (defs, expr_var_map, a) = to_defs_and_a expr_var_map ast in
        let var = Variable.create ~binding:true name in
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
        Bind ((), v, d, nf)
      ) (Var x)
    in
    
    let (defs, _, x) = to_defs_and_x expr_var_map ast in
    defs_and_x_to_e defs x

  in aux ExprMap.empty ast
