open Cduce
open Msc
open Types_additions
(*open Variable*)
open Utils

exception Ill_typed of Position.t list * string

let typeof_const_atom tenv c =
  match c with
  | Ast.Atom str -> get_type tenv str
  | c -> Ast.const_to_typ c

let typeof _ _ _ _ = failwith "TODO"
let typeof_a _ _ _ _ _ = failwith "TODO"

let refine_a tenv env a t =
  if has_absent t then [env]
  else match a with
  | Abstract s -> if disjoint s t then [] else [env]
  | Const c -> if disjoint (typeof_const_atom tenv c) t then [] else [env]
  | Pair (v1, v2) ->
    split_pair t
    |> List.filter_map (
      fun (t1, t2) ->
        env |>
        option_chain [Env_refinement.refine v1 t1 ; Env_refinement.refine v2 t2]
    )
  | Projection (Fst, v) -> [Env_refinement.refine v (mk_times (cons t) any_node) env] |> filter_options
  | Projection (Snd, v) -> [Env_refinement.refine v (mk_times any_node (cons t)) env] |> filter_options
  | Projection (Field label, v) ->
    [Env_refinement.refine v (mk_record true [label, cons t]) env] |> filter_options
  | RecordUpdate (v, label, None) ->
    let t = cap_o t (record_any_without label) in
    split_record t
    |> List.filter_map (
      fun ti ->
          let ti = remove_field_info ti label in
          Env_refinement.refine v ti env
    )
  | RecordUpdate (v, label, Some x) ->
    split_record t
    |> List.filter_map (
      fun ti ->
        let field_type = get_field_assuming_not_absent ti label in
        let ti = remove_field_info ti label in
        env |>
        option_chain [Env_refinement.refine v ti ; Env_refinement.refine x field_type]
      )
  | App (v1, v2) ->
    let t1 = Env_refinement.find v1 env in
    square_split t1 t
    |> List.filter_map (
      fun (t1, t2) ->
        env |>
        option_chain [Env_refinement.refine v1 t1 ; Env_refinement.refine v2 t2]
    )
  | Ite (v, s, x1, x2) ->
    [ env |> option_chain [Env_refinement.refine v s       ; Env_refinement.refine x1 t] ;
      env |> option_chain [Env_refinement.refine v (neg s) ; Env_refinement.refine x2 t] ]
    |> filter_options
  | Lambda _ ->
    if disjoint arrow_any t then [] else [env]
  | Let (v1, v2) ->
    [ env |>
    option_chain [Env_refinement.refine v1 any ; Env_refinement.refine v2 t]]
    |> filter_options

let infer _ _ _ _ = failwith "TODO"

let typeof_simple _ _ _ = failwith "TODO"
