open Types_additions
open Variable

type varname = string
type exprid = int

type annotation = exprid Position.located

type const =
| Unit
| EmptyRecord
| Bool of bool
| Int of int
| Char of char
| Atom of string
[@@deriving show]

type projection = Fst | Snd | Field of string
[@@deriving show]

type 'typ type_annot = Unnanoted | ADomain of 'typ | AArrow of 'typ
[@@deriving show]

type ('a, 'typ, 'v) ast =
| Abstract of 'typ
| Const of const
| Var of 'v
| Lambda of ('typ type_annot) * 'v * ('a, 'typ, 'v) t
| Ite of ('a, 'typ, 'v) t * 'typ * ('a, 'typ, 'v) t * ('a, 'typ, 'v) t
| App of ('a, 'typ, 'v) t * ('a, 'typ, 'v) t
| Let of 'v * ('a, 'typ, 'v) t * ('a, 'typ, 'v) t
| Pair of ('a, 'typ, 'v) t * ('a, 'typ, 'v) t
| Projection of projection * ('a, 'typ, 'v) t
| RecordUpdate of ('a, 'typ, 'v) t * string * ('a, 'typ, 'v) t option
| Debug of string * ('a, 'typ, 'v) t

and ('a, 'typ, 'v) t = 'a * ('a, 'typ, 'v) ast

type annot_expr = (annotation, Cduce.typ, Variable.t) t
type expr = (unit, Cduce.typ, Variable.t) t
type parser_expr = (annotation, type_expr, varname) t

module Expr = struct
    type t = expr
    let compare = compare
    let equiv t1 t2 = (compare t1 t2) = 0
end
module ExprMap = Map.Make(Expr)

type name_var_map = Variable.t StrMap.t

let empty_name_var_map = StrMap.empty

let unique_exprid =
    let last_id = ref 0 in
    fun _ -> (
        last_id := !last_id + 1 ;
        !last_id
    )
let identifier_of_expr (a,_) = Position.value a
let position_of_expr (a,_) = Position.position a

let new_annot p =
    Position.with_pos p (unique_exprid ())

let copy_annot a =
    new_annot (Position.position a)

let parser_expr_to_annot_expr tenv name_var_map e =
    let rec aux env ((exprid,pos),e) =
        let e = match e with
        | Abstract t -> Abstract (type_expr_to_typ tenv t)
        | Const c -> Const c
        | Var str ->
            if has_type_or_atom tenv str
            then Const (Atom str)
            else (
                assert (StrMap.mem str env) ;
                Var (StrMap.find str env)
            )
        | Lambda (t,str,e) ->
            let t = match t with
            | Unnanoted -> Unnanoted
            | ADomain t -> ADomain (type_expr_to_typ tenv t)
            | AArrow t -> AArrow (type_expr_to_typ tenv t)
            in
            let var = Variable.create (Some str) in
            Variable.attach_location var pos ;
            let env = StrMap.add str var env in
            Lambda (t, var, aux env e)
        | Ite (e, t, e1, e2) ->
            let t = type_expr_to_typ tenv t in
            if is_test_type t
            then Ite (aux env e, t, aux env e1, aux env e2)
            else failwith "Cannot make a typecase with a non-trvial arrow type."
        | App (e1, e2) ->
            App (aux env e1, aux env e2)
        | Let (str, e1, e2) ->
            let var = Variable.create (Some str) in
            Variable.attach_location var pos ;
            let env' = StrMap.add str var env in
            Let (var, aux env e1, aux env' e2)
        | Pair (e1, e2) ->
            Pair (aux env e1, aux env e2)
        | Projection (p, e) -> Projection (p, aux env e)
        | RecordUpdate (e1, l, e2) ->
            RecordUpdate (aux env e1, l, Utils.option_map (aux env) e2)
        | Debug (str, e) -> Debug (str, aux env e)
        in
        ((exprid,pos),e)
    in
    aux name_var_map e

let rec unannot (_,e) =
    let e = match e with
    | Abstract t -> Abstract t
    | Const c -> Const c
    | Var v -> Var v
    | Lambda (t, v, e) -> Lambda (t, v, unannot e)
    | Ite (e, t, e1, e2) -> Ite (unannot e, t, unannot e1, unannot e2)
    | App (e1, e2) -> App (unannot e1, unannot e2)
    | Let (v, e1, e2) -> Let (v, unannot e1, unannot e2)
    | Pair (e1, e2) -> Pair (unannot e1, unannot e2)
    | Projection (p, e) -> Projection (p, unannot e)
    | RecordUpdate (e1, l, e2) ->
        RecordUpdate (unannot e1, l, Utils.option_map unannot e2)
    | Debug (str, e) -> Debug (str, unannot e)
    in
    ( (), e )

let normalize_bvs e =
    let rec aux depth map (a, e) =
        let e = match e with
        | Abstract t -> Abstract t
        | Const c -> Const c
        | Var v when VarMap.mem v map -> Var (VarMap.find v map)
        | Var v -> Var v
        | Lambda (t, v, e) ->
            let v' = get_predefined_var depth in
            let map = VarMap.add v v' map in
            Lambda (t, v', aux (depth+1) map e)
        | Ite (e, t, e1, e2) ->
            Ite (aux depth map e, t, aux depth map e1, aux depth map e2)
        | App (e1, e2) ->
            App (aux depth map e1, aux depth map e2)
        | Let (v, e1, e2) ->
            let v' = get_predefined_var depth in
            let map = VarMap.add v v' map in
            Let (v', aux (depth+1) map e1, aux (depth+1) map e2)
        | Pair (e1, e2) ->
            Pair (aux depth map e1, aux depth map e2)
        | Projection (p, e) -> Projection (p, aux depth map e)
        | RecordUpdate (e1, l, e2) ->
            RecordUpdate (aux depth map e1, l, Utils.option_map (aux depth map) e2)
        | Debug (str, e) -> Debug (str, aux depth map e)
        in (a, e)
    in aux 0 VarMap.empty e

let unannot_and_normalize e = e |> unannot |> normalize_bvs

(*let rec fv (_, expr) =
  match expr with
  | Abstract _ | Const _ -> VarSet.empty
  | Var v -> VarSet.singleton v
  | Lambda (_, v, e) -> VarSet.remove v (fv e)
  | Ite (e, _, e1, e2) -> VarSet.union (VarSet.union (fv e) (fv e1)) (fv e2)
  | App (e1, e2) -> VarSet.union (fv e1) (fv e2)
  | Let (v, e1, e2) -> VarSet.union (fv e1) (VarSet.remove v (fv e2))
  | Pair (e1, e2) -> VarSet.union (fv e1) (fv e2)
  | Projection (_, e) -> fv e
  | RecordUpdate (e1, _, e2) ->
    begin match e2 with
    | Some e2 -> VarSet.union (fv e1) (fv e2)
    | None -> fv e1
    end
  | Debug (_, e) -> fv e*)

let substitute aexpr v (annot', expr') =
  let rec aux (_, expr) =
    let expr = match expr with
    | Abstract t -> Abstract t
    | Const c -> Const c
    | Var v' when Variable.equals v v' -> expr'
    | Var v' -> Var v'
    | Lambda (ta, v', e) when Variable.equals v v' -> Lambda (ta, v', e)
    | Lambda (ta, v', e) -> Lambda (ta, v', aux e)
    | Ite (e, t, e1, e2) -> Ite (aux e, t, aux e1, aux e2)
    | App (e1, e2) -> App (aux e1, aux e2)
    | Let (v', e1, e2) when Variable.equals v v' -> Let (v', aux e1, e2)
    | Let (v', e1, e2) -> Let (v', aux e1, aux e2)
    | Pair (e1, e2) -> Pair (aux e1, aux e2)
    | Projection (p, e) -> Projection (p, aux e)
    | RecordUpdate (e1, f, e2) ->
      let e2 = match e2 with
      | Some e2 -> Some (aux e2)
      | None -> None
      in RecordUpdate (aux e1, f, e2)
    | Debug (str, e) -> Debug (str, aux e)
    in
    (annot', expr)
  in aux aexpr

let const_to_typ c =
    match c with
    | Unit -> Cduce.unit_typ
    | EmptyRecord -> Cduce.empty_closed_record
    | Bool true -> Cduce.true_typ
    | Bool false -> Cduce.false_typ
    | Int i -> Cduce.interval (Some i) (Some i)
    | Char c -> Cduce.single_char c
    | Atom t ->
        failwith (Printf.sprintf "Can't retrieve the type of the atom %s." t)

type parser_element =
| Definition of (string * parser_expr)
| Atoms of string list
| Types of (string * type_expr) list

type parser_program = parser_element list
