
module CD = Cduce_types

type typ = CD.Types.t
type node = CD.Types.Node.t
type var = CD.Var.t

val dump_typ : Format.formatter -> typ -> unit
val pp_typ : Format.formatter -> typ -> unit
val show_typ : typ -> string
val pp_var : Format.formatter -> var -> unit

val register : string -> typ -> unit
val pp : Format.formatter -> typ -> unit
val string_of_type : typ -> string
val pp_node : Format.formatter -> node -> unit
val descr : node -> typ
val cons : typ -> node

val any : typ
val empty : typ
val any_node : node
val empty_node : node

val true_typ : typ
val false_typ : typ
val bool_typ : typ
val int_typ : typ
val char_typ : typ
val unit_typ : typ
val nil_typ : typ
val string_typ : typ
val list_typ : typ
val interval : int option -> int option -> typ
val single_char : char -> typ
val single_string : string -> typ
val var_typ : var -> typ

val neg : typ -> typ
val cup : typ -> typ -> typ
val cap : typ -> typ -> typ
val diff : typ -> typ -> typ
val cup_o : typ -> typ -> typ
val cap_o : typ -> typ -> typ
val diff_o : typ -> typ -> typ

val mk_atom : string -> typ
val mk_new_typ: unit -> node
val define_typ: node -> typ -> unit
(*val normalize_typ: typ -> typ*)

module Iter = CD.Types.Iter
module type Kind = CD.Types.Kind


val mk_times : node -> node -> typ
val pair_any : typ
val pi1 : typ -> typ
val pi2 : typ -> typ
val split_pair : typ -> (typ * typ) list

val to_label : string -> Ns.Label.t
val from_label : Ns.Label.t -> string
val mk_record : bool (* is_open *) -> (string * node) list -> typ
val record_any : typ
val absent : typ
val has_absent : typ -> bool
val any_or_absent : typ
val absent_node : node
val any_or_absent_node : node
val or_absent : typ -> typ
val empty_closed_record : typ
val empty_open_record : typ
val get_field : typ -> string -> typ (* Can raise Not_found *)
val get_field_assuming_not_absent : typ -> string -> typ
val merge_records : typ -> typ -> typ
val remove_field : typ -> string -> typ

val mk_arrow : node -> node -> typ
val arrow_any : typ
val domain : typ -> typ
val apply : typ -> typ -> typ
val dnf : typ -> (typ * typ) list list

module type TVarSet = sig
    type t
    val empty : t
    val construct : var list -> t
    val is_empty : t -> bool
    val mem : t -> var -> bool
    val filter : (var -> bool) -> t -> t
    val union : t -> t -> t
    val add : var -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val rm : var -> t -> t
    val destruct : t -> var list
    val pp : Format.formatter -> t -> unit
end
module TVarSet : TVarSet

val mk_var : string -> var
val var_equal : var -> var -> bool
val var_compare : var -> var -> int
val vars : typ -> TVarSet.t
val top_vars : typ -> TVarSet.t
val vars_with_polarity : typ -> (var * [ `Both | `Neg | `Pos ]) list
val var_name : var -> string
val check_var : typ -> [ `Not_var | `Pos of var | `Neg of var ]

type subst
module type Subst = sig
    type t = subst
    val construct : (var * typ) list -> t
    val identity : t
    val is_identity : t -> bool
    val dom : t -> TVarSet.t
    val mem : t -> var -> bool
    val rm: var -> t -> t
    val find : t -> var -> typ
    val equiv : t -> t -> bool
    val apply : t -> typ -> typ
    val destruct : t -> (var * typ) list
    val pp : Format.formatter -> t -> unit
end
module Subst : Subst

val is_empty : typ -> bool
val non_empty: typ -> bool
val subtype  : typ -> typ -> bool
val disjoint : typ -> typ -> bool
val equiv : typ -> typ -> bool

val inf_typ : TVarSet.t -> typ -> typ
val sup_typ : TVarSet.t -> typ -> typ

(* Tallying *)
val clean_type : pos:typ -> neg:typ -> TVarSet.t -> typ -> typ
val rectype : typ -> var -> typ (* [rectype t u] returns the type corresponding to the equation u=t *)
val refresh : TVarSet.t -> typ -> typ
(* Variables not in var_order are considered greater. In the result, a variable will be expressed
in term of the variables that are greater. Thus, greater variables (in particular variables not in var_order)
are less likely to be constrained. *)
val tallying : var_order:var list -> TVarSet.t -> (typ * typ) list -> Subst.t list
