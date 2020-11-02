
type typ = Cduce.typ
module ExprMap = Ast.ExprMap

module Variable = struct

  let data = Hashtbl.create 100

  type t = int
  let compare = compare
  let equals a b = a = b

  let next_id =
    let last = ref 0 in
    fun () ->
      last := !last + 1 ;
      !last

  let create display_name =
    let id = next_id () in
    Hashtbl.add data id (display_name, []) ;
    id

  let attach_location id loc =
    let (name, locs) = Hashtbl.find data id in
    Hashtbl.replace data id (name, loc::locs)

  let get_locations id =
    let (_, locs) = Hashtbl.find data id
    in locs

  let get_name id =
    let (name, _) = Hashtbl.find data id
    in name
end

module VarMap = Map.Make(Variable)
module SetMap = Set.Make(Variable)

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

(* TODO: test if ast is already in expr_var_map (in order to factorize common sub-expressions) *)
let convert_to_normal_form expr_var_map ast =
  let rec aux expr_var_map ast =
    let rec to_defs_and_a expr_var_map ast =
      let ((_, pos), e) = ast in
      match e with
      | Ast.Const c -> ([], expr_var_map, Const c)
      | Ast.Var v ->
        assert (ExprMap.mem ((), Ast.Var v) expr_var_map) ;
        ([], expr_var_map, Var (ExprMap.find ((), Ast.Var v) expr_var_map))
      | Ast.Lambda (t, v, e) ->
        let var = Variable.create None in
        Variable.attach_location var pos ;
        let e = aux (ExprMap.add ((), Ast.Var v) var expr_var_map) e in
        ([], expr_var_map, Lambda (t, var, e))
      | Ast.Ite (e, t, e1, e2) ->
        let (defs, expr_var_map, x) = to_defs_and_x expr_var_map e in
        let nf1 = aux expr_var_map e1 in
        let nf2 = aux expr_var_map e2 in
        (defs, expr_var_map, Ite (x, t, nf1, nf2))
      | Ast.Let (v, e1, e2) ->
        let var = Variable.create None in
        Variable.attach_location var pos ;
        let (defs1, expr_var_map, a1) = to_defs_and_a expr_var_map e1 in
        let expr_var_map = ExprMap.add ((), Ast.Var v) var expr_var_map in
        let defs1 = (var, a1)::defs1 in
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

  in aux expr_var_map ast
