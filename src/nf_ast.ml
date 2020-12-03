open Variable
module ExprMap = Ast.ExprMap

type a =
  | Const of Ast.const
  | Var of Variable.t
  | Lambda of (Cduce.typ Ast.type_annot) * Variable.t * e
  | Ite of Variable.t * Cduce.typ * e * e
  | App of Variable.t * Variable.t
  | Pair of Variable.t * Variable.t
  | Projection of Ast.projection * Variable.t
  | RecordUpdate of Variable.t * string * Variable.t option
  | Debug of string * Variable.t
  [@@deriving show]

and e =
  | Let of Variable.t * a * e
  | EVar of Variable.t
  | Hole
  [@@deriving show]

let convert_to_normal_form ast =
  let rec aux expr_var_map ast =
    let rec to_defs_and_a expr_var_map ast =
      let (_, e) = ast in
      let uast = Ast.unannot ast in
      if ExprMap.mem uast expr_var_map
      then ([], expr_var_map, Var (ExprMap.find uast expr_var_map))
      else match e with
      | Ast.Const c -> ([], expr_var_map, Const c)
      | Ast.Var v -> ([], expr_var_map, Var v)
      | Ast.Lambda (t, v, e) ->
        let e = aux expr_var_map e in
        ([], expr_var_map, Lambda (t, v, e))
      | Ast.Ite (e, t, e1, e2) ->
        let (defs, expr_var_map, x) = to_defs_and_x expr_var_map e in
        let nf1 = aux expr_var_map e1 in
        let nf2 = aux expr_var_map e2 in
        (defs, expr_var_map, Ite (x, t, nf1, nf2))
      | Ast.Let (v, e1, e2) ->
        let (defs1, expr_var_map, a1) = to_defs_and_a expr_var_map e1 in
        let defs1 = (v, a1)::defs1 in
        let expr_var_map = ExprMap.add (Ast.unannot e1) v expr_var_map in
        let (defs2, expr_var_map, a2) = to_defs_and_a expr_var_map e2 in
        (defs2@defs1, expr_var_map, a2)
      | Ast.App (e1, e2) ->
        let (defs1, expr_var_map, x1) = to_defs_and_x expr_var_map e1 in (* TODO: check order according to the semantics *)
        let (defs2, expr_var_map, x2) = to_defs_and_x expr_var_map e2 in
        (defs2@defs1, expr_var_map, App (x1, x2))
      | Ast.Pair (e1, e2) ->
        let (defs1, expr_var_map, x1) = to_defs_and_x expr_var_map e1 in (* TODO: check order according to the semantics *)
        let (defs2, expr_var_map, x2) = to_defs_and_x expr_var_map e2 in
        (defs2@defs1, expr_var_map, Pair (x1, x2))
      | Ast.Projection (p, e) ->
        let (defs, expr_var_map, x) = to_defs_and_x expr_var_map e in
        (defs, expr_var_map, Projection (p, x))
      | Ast.RecordUpdate (e, str, None) ->
        let (defs, expr_var_map, x) = to_defs_and_x expr_var_map e in
        (defs, expr_var_map, RecordUpdate (x, str, None))
      | Ast.RecordUpdate (e, str, Some e') ->
        let (defs, expr_var_map, x) = to_defs_and_x expr_var_map e in (* TODO: check order according to the semantics *)
        let (defs', expr_var_map, x') = to_defs_and_x expr_var_map e' in
        (defs'@defs, expr_var_map, RecordUpdate (x, str, Some x'))
      | Ast.Debug (str, e) ->
        let (defs, expr_var_map, x) = to_defs_and_x expr_var_map e in
        (defs, expr_var_map, Debug (str, x))

    and to_defs_and_x expr_var_map ast =
      let ((_, pos), _) = ast in
      let (defs, expr_var_map, a) = to_defs_and_a expr_var_map ast in
      match a with
      | Var v -> (defs, expr_var_map, v)
      | a ->
        let var = Variable.create None in
        Variable.attach_location var pos ;
        let expr_var_map = ExprMap.add (Ast.unannot ast) var expr_var_map in
        let defs = (var, a)::defs in
        (defs, expr_var_map, var)
    in
    let (defs, _, x) = to_defs_and_x expr_var_map ast in
    defs |>
    List.fold_left (
      fun nf (v, d) ->
      Let (v, d, nf)
    ) (EVar x)

  in aux ExprMap.empty ast

let convert_a_to_e a pos =
  let var = Variable.create None in
  List.iter (fun pos -> Variable.attach_location var pos) pos ;
  Let (var, a, EVar var)

let map ef af =
  let rec aux_a a =
    begin match a with
    | Const c -> Const c
    | Var v -> Var v
    | Lambda (ta, v, e) -> Lambda (ta, v, aux_e e)
    | Ite (v, t, e1, e2) -> Ite (v, t, aux_e e1, aux_e e2)
    | App (v1, v2) -> App (v1, v2)
    | Pair (v1, v2) -> Pair (v1, v2)
    | Projection (p, v) -> Projection (p, v)
    | RecordUpdate (v, str, vo) -> RecordUpdate (v, str, vo)
    | Debug (str, v) -> Debug (str, v)
    end
    |> af
  and aux_e e =
    begin match e with
    | Let (v, a, e) -> Let (v, aux_a a, aux_e e)
    | EVar v -> EVar v
    | Hole -> Hole
    end
    |> ef
  in (aux_e, aux_a)

let map_e ef af = map ef af |> fst
let map_a ef af = map ef af |> snd

let fold ef af =
  let rec aux_a a =
    begin match a with
    | Const _ | Var _ | Debug _ | App _ | Pair _ | Projection _ | RecordUpdate _ -> []
    | Lambda (_, _, e) -> [aux_e e]
    | Ite (_, _, e1, e2) -> [aux_e e1 ; aux_e e2]
    end
    |> af a
  and aux_e e =
    begin match e with
    | Let (_, a, e) -> [aux_a a ; aux_e e]
    | EVar _ | Hole -> []
    end
    |> ef e
  in (aux_e, aux_a)

let fold_e ef af = fold ef af |> fst
let fold_a ef af = fold ef af |> snd
