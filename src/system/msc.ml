open Parsing
open Parsing.Variable
module ExprMap = Parsing.Ast.ExprMap
open Types.Base
open Types.Tvar

type a =
  | Alias of Variable.t
  | Abstract of typ
  | Const of Ast.const
  | Lambda of (typ list) * Variable.t * e
  | Ite of Variable.t * typ * Variable.t * Variable.t
  | App of Variable.t * Variable.t
  | Pair of Variable.t * Variable.t
  | Projection of Ast.projection * Variable.t
  | RecordUpdate of Variable.t * string * Variable.t option
  | Let of Variable.t * Variable.t
  | TypeConstr of Variable.t * typ
  [@@deriving show]

and e =
  | Bind of Variable.t * a * e
  | Var of Variable.t
  [@@deriving show]

let fixpoint_var = Variable.create_other (Some "__builtin_fixpoint")
let fixpoint_typ =
  let a = TVar.mk_poly None |> TVar.typ |> cons in
  let b = TVar.mk_poly None |> TVar.typ |> cons in
  let f = mk_arrow a b in
  let c = TVar.mk_poly None |> TVar.typ in
  let fc = cap f c |> cons in
  let arg = mk_arrow (cons f) fc |> cons in
  mk_arrow arg fc
let initial_env =
  Env.construct [(fixpoint_var, fixpoint_typ)]

let map ef af =
  let rec aux_a a =
    begin match a with
    | Alias v -> Alias v
    | Abstract t -> Abstract t
    | Const c -> Const c
    | Lambda (ta, v, e) -> Lambda (ta, v, aux_e e)
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
    | Alias _ | Abstract _ | Const _ | App _ | Pair _
    | Projection _ | RecordUpdate _ | Ite _ | Let _
    | TypeConstr _ -> []
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

let fv_e' e acc =
  let acc = List.fold_left VarSet.union VarSet.empty acc in
  match e with
  | Bind (v, _, _) -> VarSet.remove v acc
  | Var v -> VarSet.add v acc
let fv_a' a acc =
  let acc = List.fold_left VarSet.union VarSet.empty acc in
  match a with
  | Lambda (_, v, _) -> VarSet.remove v acc
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
  match e with Bind (v, _, _) -> VarSet.add v acc | Var _ -> acc
let bv_a' a acc =
  let acc = List.fold_left VarSet.union VarSet.empty acc in
  match a with Lambda (_, v, _) -> VarSet.add v acc | _ -> acc

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

let rec type_of_pat pat =
  let open Ast in
  match pat with
  | PatType t -> t
  | PatVar _ -> any
  | PatAnd (p1, p2) ->
    cap (type_of_pat p1) (type_of_pat p2)
  | PatOr (p1, p2) ->
    cup (type_of_pat p1) (type_of_pat p2)
  | PatPair (p1, p2) ->
    mk_times (type_of_pat p1 |> cons) (type_of_pat p2 |> cons)
  | PatRecord (fields, o) ->
    mk_record o (List.map (fun (str, p) -> (str, type_of_pat p |> cons)) fields)
  | PatAssign _ -> any

let rec vars_of_pat pat =
  let open Ast in
  match pat with
  | PatType _ -> VarSet.empty
  | PatVar x when Variable.equals x dummy_pat_var -> VarSet.empty
  | PatVar x -> VarSet.singleton x
  | PatAnd (p1, p2) ->
    VarSet.union (vars_of_pat p1) (vars_of_pat p2)
  | PatOr (p1, p2) ->
    VarSet.inter (vars_of_pat p1) (vars_of_pat p2)
  | PatPair (p1, p2) ->
    VarSet.union (vars_of_pat p1) (vars_of_pat p2)
  | PatRecord (fields, _) ->
    List.fold_left
      (fun acc (_, p) -> VarSet.union acc (vars_of_pat p))
      VarSet.empty fields
  | PatAssign (x,_) -> VarSet.singleton x

let rec def_of_var_pat pat v e =
  assert (Variable.equals v Ast.dummy_pat_var |> not) ;
  let open Ast in
  let (annot, _) = e in
  match pat with
  | PatVar v' when Variable.equals v v' -> e
  | PatVar _ -> assert false
  | PatAnd (p1, p2) ->
    if vars_of_pat p1 |> VarSet.mem v
    then def_of_var_pat p1 v e
    else def_of_var_pat p2 v e
  | PatPair (p1, p2) ->
    if vars_of_pat p1 |> VarSet.mem v
    then def_of_var_pat p1 v (annot, Projection (Fst, e))
    else def_of_var_pat p2 v (annot, Projection (Snd, e))
  | PatRecord (fields, _) ->
    let (str, p) =
      fields |> List.find (fun (_, p) -> vars_of_pat p |> VarSet.mem v)
    in
    def_of_var_pat p v (annot, Projection (Field str, e))
  | PatOr (p1, p2) ->
    let case = Ite (e, type_of_pat p1,
      def_of_var_pat p1 v e, def_of_var_pat p2 v e) in
    (annot, case)
  | PatAssign (v', c) when Variable.equals v v' -> (annot, Const c)
  | PatAssign _ -> assert false
  | PatType _ -> assert false

let remove_patterns_and_fixpoints e =
  let aux (annot,e) =
    let e =
      match e with
      | Ast.PatMatch (e, pats) ->
        let t = pats |> List.map fst |> List.map type_of_pat
          |> Types.Additions.disj in
        let body_of_pat pat e' =
          let vars = vars_of_pat pat in
          let add_def acc v =
            let d = def_of_var_pat pat v e in
            (annot, Ast.Let (v, d, acc))
          in
          List.fold_left add_def e' (VarSet.elements vars)
        in
        let add_branch acc (t, e') =
          (annot, Ast.Ite (e, t, e', acc))
        in
        let pats = pats |> List.map (fun (pat, e') ->
          (type_of_pat pat, body_of_pat pat e')) |> List.rev in
        let body = match pats with
        | [] -> assert false 
        | (_, e')::pats -> List.fold_left add_branch e' pats
        in
        let x = Variable.create_other None in
        Variable.attach_location x (Position.position annot) ;
        Ast.Let (x, (annot, Ast.TypeConstr (e, t)), body)
      | Ast.Fixpoint e ->
        let lhs = (annot, Ast.Var fixpoint_var) in
        let rhs = (annot, Ast.TopLevel e) in
        Ast.App (lhs, rhs)
      | e -> e
    in
    (annot, e)
  in
  Ast.map_ast aux e

let vhole = Variable.create_lambda None
let vhole_ann = (Ast.new_annot Position.dummy, Ast.Var vhole)
let insert_in_ctx e' e = Ast.substitute e vhole e'
let remove_toplevel e =
  let open Ast in
  let ctx = vhole_ann in
  let es = ref [] in
  let rec aux ctx cur_args (annot,e) =
    let aux' = aux ctx cur_args in
    let e = match e with
    | TopLevel e ->
      let e = aux' e in
      let e' = insert_in_ctx e ctx in
      let x = Variable.create_other (Some "toplevel_aux") in
      Variable.attach_location x (Position.position annot) ;
      es := (x,e')::!es ;
      let app = List.fold_right
        (fun arg acc -> App ((annot, acc), (annot, Var arg)))
        cur_args (Var x) in
      app
    | Lambda (ts, v, e) ->
      let ctx = insert_in_ctx
        (annot, Lambda (ts, v, vhole_ann)) ctx in
      let cur_args = v::cur_args in
      Lambda (ts, v, aux ctx cur_args e)
    | Abstract t -> Abstract t
    | Const c -> Const c
    | Var v -> Var v
    | Ite (e, t, e1, e2) -> Ite (aux' e, t, aux' e1, aux' e2)
    | App (e1, e2) -> App (aux' e1, aux' e2)
    | Let (v, e1, e2) -> Let (v, aux' e1, aux' e2)
    | Pair (e1, e2) -> Pair (aux' e1, aux' e2)
    | Projection (p, e) -> Projection (p, aux' e)
    | RecordUpdate (e, str, eo) ->
      RecordUpdate (aux' e, str, Option.map aux' eo)
    | TypeConstr (e, t) -> TypeConstr (aux' e, t)
    | Fixpoint _ | PatMatch _ -> assert false
    in
    (annot, e)
  in
  let e = aux ctx [] e in
  (e, List.rev !es)  
  
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
        let ts = match t with
        | Unnanoted -> [ TVar.mk_mono ~infer:true (Variable.get_name v) |> TVar.typ ]
        | ADomain ts -> ts
        in
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
        (defs, expr_var_map, Lambda (ts, v, e))
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
      | Ast.PatMatch _ | Ast.Fixpoint _ | Ast.TopLevel _ -> assert false

    and to_defs_and_x ?(name=None) expr_var_map ast =
      let ((_, pos), _) = ast in
      try
        let (defs, expr_var_map, a) = to_defs_and_a expr_var_map ast in
        let var = Variable.create_binding name in
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

(* let remove_useless_bindings e =
  let remove_useless e =
    match e with
    | Bind (v, a, e) when VarSet.mem v (fv_e e) -> Bind (v, a, e)
    | Bind (_, _, e) -> e
    | Var v -> Var v
  in
  map_e remove_useless Utils.identity e *)
