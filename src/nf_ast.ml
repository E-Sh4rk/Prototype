open Variable
type typ = Cduce.typ
module ExprMap = Ast.ExprMap

type a =
  | Const of Ast.const
  | Var of Variable.t
  | Lambda of (typ Ast.type_annot) * Variable.t * e
  | Ite of Variable.t * typ * e * e
  | App of Variable.t * Variable.t
  | Pair of Variable.t * Variable.t
  | Projection of Ast.projection * Variable.t
  | RecordUpdate of Variable.t * string * Variable.t option
  | Debug of string * Variable.t

and e =
  | Let of Variable.t * a * e
  | Atomic of a

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
    let (defs, _, a) = to_defs_and_a expr_var_map ast in
    List.rev defs |>
    List.fold_left (
      fun nf (v, d) ->
      Let (v, d, nf)
    ) (Atomic a)

  in aux ExprMap.empty ast
