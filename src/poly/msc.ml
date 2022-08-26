
type a = unit Common.Msc.a
[@@deriving show]
type e = unit Common.Msc.e
[@@deriving show]

let contains_records e =
  let open Common.Msc in
  let rec aux e =
    match e with
    | Var _ -> false
    | Bind (_,_,a,e) -> aux_a a || aux e
  and aux_a a =
    match a with
    | Abstract t -> aux_t t
    | Const EmptyRecord -> true
    | Const _ -> false
    | Lambda (_, Parsing.Ast.Unnanoted, _, e) -> aux e
    | Lambda (_, Parsing.Ast.AArrow t, _, e)
    | Lambda (_, Parsing.Ast.ADomain t, _, e) -> aux_t t || aux e
    | Ite (_, s, _, _) -> aux_t s
    | Projection (Parsing.Ast.Field _, _)
    | RecordUpdate _ -> true
    | App _ | Pair _ | Projection _ | Let _ -> false
  and aux_t _ = false (* TODO: Implement contains_records for types *)
  in
  aux e
