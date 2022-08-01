open Common.Msc
open Old_annotations

type a = VarAnnot.t Common.Msc.a
[@@deriving show]
type e = VarAnnot.t Common.Msc.e
[@@deriving show]

let convert_to_msc ~legacy ast =
  let unannotated = convert_to_msc ast in
  let annot_e () = VarAnnot.initial_binding ~legacy in
  let annot_a () = VarAnnot.initial_lambda ~legacy in
  map_annot_e annot_e annot_a unannotated

let merge_annots' =
let rec aux_a a1 a2 =
  match a1, a2 with
  | Abstract t, _ -> Abstract t
  | Const c, _ -> Const c
  | Lambda (va1, t, v, e1), Lambda (va2, _, _, e2) ->
    Lambda (VarAnnot.cup va1 va2, t, v, aux_e e1 e2)
  | Lambda _, _ -> assert false
  | Ite (v, t, x1, x2), _ -> Ite (v, t, x1, x2)
  | App (v1, v2), _ -> App (v1, v2)
  | Pair (v1, v2), _ -> Pair (v1, v2)
  | Projection (p, v), _ -> Projection (p, v)
  | RecordUpdate (v, str, vo), _ -> RecordUpdate (v, str, vo)
  | Let (v1, v2), _ -> Let (v1, v2)
and aux_e e1 e2 =
  match e1, e2 with
  | Var v, _ -> Var v
  | Bind (va1, v, a1, e1), Bind (va2, _, a2, e2) ->
    Bind (VarAnnot.cup va1 va2, v, aux_a a1 a2, aux_e e1 e2)
  | Bind _, _ -> assert false
in
(aux_a, aux_e)

let merge_annots_a' = merge_annots' |> fst
let merge_annots_e' = merge_annots' |> snd

let merge_annots_a a_s =
match a_s with
| [] -> raise Not_found
| a::a_s -> List.fold_left merge_annots_a' a a_s
let merge_annots_e es =
match es with
| [] -> raise Not_found
| e::es -> List.fold_left merge_annots_e' e es
