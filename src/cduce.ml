
module CD = Cduce_types
module LabelSet = CD.Ident.LabelSet
module LabelMap = CD.Ident.LabelMap

type typ = CD.Types.t
type node = CD.Types.Node.t

let register s = 
  let module U = Encodings.Utf8 in
  CD.Types.Print.register_global "" (Ns.Uri.mk (U.mk ""), U.mk s)
let pp_typ = CD.Types.Print.print_noname
let show_typ t = Format.asprintf "%a" pp_typ t

let pp = pp_typ
let string_of_type = CD.Types.Print.to_string
let pp_node = CD.Types.Print.print_node
let descr = CD.Types.descr
let cons = CD.Types.cons


let any = CD.Types.any
let empty = CD.Types.empty
let any_node = CD.Types.any_node
let empty_node = CD.Types.empty_node

(* ----- *)

let is_empty = CD.Types.is_empty
let non_empty = CD.Types.non_empty
let subtype = CD.Types.subtype
let disjoint = CD.Types.disjoint
let equiv = CD.Types.equiv

let cup t1 t2 = CD.Types.cup t1 t2
let cap t1 t2 = CD.Types.cap t1 t2
let diff = CD.Types.diff
let neg = CD.Types.neg

(* NOTE: arrow types are not automatically simplified by Cduce,
   thus we avoid useless cap\cup in order to keep simple types *)
let cup_o t1 t2 = if subtype t1 t2 then t2
else if subtype t2 t1 then t1 else CD.Types.cup t1 t2
let cap_o t1 t2 = if subtype t1 t2 then t1
else if subtype t2 t1 then t2 else CD.Types.cap t1 t2

(* ----- *)

let to_label str = CD.Ident.Label.mk_ascii str
let from_label lbl = CD.Ident.Label.get_ascii lbl

(* ----- *)

(*let mk_var internal name =
    let var = CD.Var.mk ~internal:internal name in
    CD.Types.var var*)

let mk_atom ascii_name =
    ascii_name |> CD.Atoms.V.mk_ascii |> CD.Atoms.atom |> CD.Types.atom
let true_typ = CD.Builtin_defs.true_type
let false_typ = CD.Builtin_defs.false_type
let bool_typ = cup true_typ false_typ
let int_typ = CD.Types.Int.any
let char_typ = CD.Types.Char.any
let unit_typ = mk_atom "unit"
let nil_typ = CD.Sequence.nil_type

let string_typ =
  let str = CD.Types.make () in
  let times = CD.Types.times (cons char_typ) str in
  let union = CD.Types.cup nil_typ times in
  CD.Types.define str union ;
  descr str

let list_typ =
  let lst = CD.Types.make () in
  let times = CD.Types.times any_node lst in
  let union = CD.Types.cup nil_typ times in
  CD.Types.define lst union ;
  descr lst

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

let single_string str =
  let rev_str =
    String.to_seq str |>
    Seq.fold_left (
      fun acc c ->
        c::acc
    ) []
  in
  List.fold_left (
    fun acc c ->
      CD.Types.times (single_char c |> cons) (cons acc)
  ) nil_typ rev_str

(*
let list_of alpha =
    let alpha_list = CD.Types.make () in
    let cons = CD.Types.times (cons alpha) alpha_list in
    let union = CD.Types.cup nil_typ cons in
    CD.Types.define alpha_list union ;
    descr alpha_list
*)

(*
let single_list lst =
  List.rev lst |>
  List.fold_left (
    fun acc t ->
      CD.Types.times (cons t) (cons acc)
  ) nil_typ
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
  CD.Types.Product.normal ~kind:`Normal t


let mk_record is_open fields =
  let fields = List.map (fun (str,node) -> (to_label str,node)) fields in
  let fields = LabelMap.from_list_disj fields in
  CD.Types.record_fields (is_open, fields)

let record_any = CD.Types.Record.any

let absent = CD.Types.Record.absent

let has_absent = CD.Types.Record.has_absent

let any_or_absent = CD.Types.Record.any_or_absent

let absent_node = CD.Types.Record.absent_node

let any_or_absent_node = CD.Types.Record.any_or_absent_node

let or_absent = CD.Types.Record.or_absent

let empty_closed_record = CD.Types.empty_closed_record

let empty_open_record = CD.Types.empty_open_record

let get_field record field =
  CD.Types.Record.project record (to_label field)

let get_field_assuming_not_absent record field =
  CD.Types.Record.project_opt record (to_label field)

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

