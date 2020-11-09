
module CD = Cduce_lib
module LabelSet = CD.Ident.LabelSet
module LabelMap = CD.Ident.LabelMap

type typ = CD.Types.t
type node = CD.Types.Node.t

let pp_typ = CD.Types.Print.pp_type
let show_typ = CD.Types.Print.string_of_type

let pp = CD.Types.Print.pp_type
let printf = CD.Types.Print.printf
let dump = CD.Types.Print.dump
let string_of_type = CD.Types.Print.string_of_type
let string_of_node = CD.Types.Print.string_of_node
let descr = CD.Types.descr
let cons = CD.Types.cons


let any = CD.Types.any
let empty = CD.Types.empty
let any_node = CD.Types.any_node
let empty_node = CD.Types.empty_node


let is_empty = CD.Types.is_empty
let non_empty = CD.Types.non_empty
let subtype = CD.Types.subtype
let disjoint = CD.Types.disjoint
let equiv = CD.Types.equiv


(* TODO: Not very optimized... but temporary fix for the fact that arrows are not simplified *)
let cup t1 t2 = if subtype t1 t2 then t2
                else if subtype t2 t1 then t1 else CD.Types.cup t1 t2
let cap t1 t2 = if subtype t1 t2 then t1
                else if subtype t2 t1 then t2 else CD.Types.cap t1 t2
let diff = CD.Types.diff
let neg = CD.Types.neg

(* ----- *)

let to_label str = CD.Ident.Label.mk_ascii str
let from_label lbl = CD.Ident.Label.get_ascii lbl

(* ----- *)

let mk_var internal name =
    let var = CD.Var.mk ~internal:internal name in
    CD.Types.var var

let mk_atom ascii_name =
    ascii_name |> CD.Atoms.V.mk_ascii |> CD.Atoms.atom |> CD.Types.atom

(*
let mk_list alpha =
    let alpha_list = CD.Types.make () in

    let nil_atom = mk_atom "nil" in
    let cons = CD.Types.times alpha alpha_list in

    let descr = CD.Types.cup nil_atom cons in
    CD.Types.define alpha_list descr ;
    alpha_list
*)

let mk_new_typ = CD.Types.make

let define_typ = CD.Types.define

let normalize_typ = CD.Types.normalize


let mk_times = CD.Types.times

let pair_any = CD.Types.Product.any

let pi1 t =
  CD.Types.Product.pi1 (CD.Types.Product.get t)

let pi2 t =
  CD.Types.Product.pi2 (CD.Types.Product.get t)

let split_pair t =
  CD.Types.Product.get ~kind:`Normal t


let mk_record is_open fields =
  let fields = List.map (fun (str,node) -> (to_label str,node)) fields in
  let fields = LabelMap.from_list_disj fields in
  CD.Types.record_fields (is_open, fields)

let record_any = CD.Types.Record.any

let absent = CD.Types.Record.absent

let any_or_absent = CD.Types.Record.any_or_absent

let absent_node = CD.Types.Record.absent_node

let any_or_absent_node = CD.Types.Record.any_or_absent_node

let or_absent = CD.Types.Record.or_absent

let empty_closed_record = CD.Types.empty_closed_record

let empty_open_record = CD.Types.empty_open_record

let get_field record field =
  CD.Types.Record.project record (to_label field)

let all_fields record =
  let lbls = CD.Types.Record.all_labels record in
  List.map from_label (LabelSet.get lbls)

let merge_records = CD.Types.Record.merge

let remove_field record field =
  CD.Types.Record.remove_field record (to_label field)


(* Maybe not optimised (if no memoisation for Arrow.get). We'll see that later. *)
let mk_arrow = CD.Types.arrow

let arrow_any = CD.Types.Arrow.any

let domain t =
  if subtype t arrow_any then
    let t = CD.Types.Arrow.get t in
    CD.Types.Arrow.domain t
  else empty

let apply t args =
  let t = CD.Types.Arrow.get t in
  CD.Types.Arrow.apply t args

let dnf t =
  snd (CD.Types.Arrow.get t)


let true_typ = mk_atom "true"
let false_typ = mk_atom "false"
let bool_typ = cup true_typ false_typ
let int_typ = CD.Types.Int.any
let char_typ = CD.Types.Char.any
let unit_typ = mk_atom "unit"

let interval i1 i2 =
  match i1, i2 with
  | Some i1, Some i2 -> 
    let i1 = CD.Intervals.V.from_int i1 in
    let i2 = CD.Intervals.V.from_int i2 in
    let i = CD.Intervals.bounded i1 i2 in
    CD.Types.interval i
  | Some i1, None ->
    let i1 = CD.Intervals.V.from_int i1 in
    let i = CD.Intervals.right i1 in
    CD.Types.interval i
  | None, Some i2 ->
    let i2 = CD.Intervals.V.from_int i2 in
    let i = CD.Intervals.left i2 in
    CD.Types.interval i
  | None, None ->
    CD.Types.Int.any
    
let single_char c =
  let c = CD.Chars.V.mk_char c in
  let c = CD.Chars.atom c in
  CD.Types.char c
