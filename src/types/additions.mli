
open Base

module StrMap : Map.S with type key = String.t

exception TypeDefinitionError of string

(* Construction of types *)

type type_base =
    | TInt of int option * int option | TSChar of char | TSString of string
    | TBool | TTrue | TFalse | TUnit | TChar | TAny | TEmpty | TNil
    | TString | TList

type type_regexp =
    | ReEpsilon | ReEmpty
    | ReType of type_expr
    | ReSeq of type_regexp * type_regexp
    | ReStar of type_regexp
    | ReAlt of type_regexp * type_regexp

and type_expr =
    | TVar of string
    | TBase of type_base
    | TCustom of string
    | TPair of type_expr * type_expr
    | TRecord of bool * (string * type_expr * bool) list
    | TSList of type_regexp
    | TArrow of type_expr * type_expr
    | TCup of type_expr * type_expr
    | TCap of type_expr * type_expr
    | TDiff of type_expr * type_expr
    | TNeg of type_expr

type type_env
type var_type_env

val empty_tenv : type_env
val empty_vtenv : var_type_env

val type_base_to_typ : type_base -> typ

val type_expr_to_typ : type_env -> var_type_env -> type_expr -> typ * var_type_env

val define_atom : type_env -> string -> type_env

val define_types : type_env -> var_type_env -> (string * type_expr) list -> type_env * var_type_env

val get_type : type_env -> string -> typ

val has_type : type_env -> string -> bool

val has_atom : type_env -> string -> bool

(* Operations on types *)

val conj : typ list -> typ
val disj : typ list -> typ
val conj_o : typ list -> typ
val disj_o : typ list -> typ

val remove_negative_arrows : typ -> typ

val simplify_dnf : (typ * typ) list list -> (typ * typ) list list
val simplify_typ : typ -> typ

val branch_type : (typ*typ) list -> typ

val is_test_type : typ -> bool

val square_split : typ -> typ -> (typ * typ) list
val square_approx : typ -> typ -> typ
val square_exact : typ -> typ -> typ

val triangle_split : typ -> typ -> (typ * typ) list
val triangle_exact : typ -> typ -> typ

(* Record manipulation *)

val record_any_with : string -> typ
(** [record_any_with l] creates the record type {l = Any ..} *)

val record_any_without : string -> typ
(** [record_any_without l] creates the record type {l =? Empty ..} *)

val split_record : typ -> typ list
(** [split_record t] splits a union of record types 
    into a list of individual record types *)

val remove_field_info : typ -> string -> typ
(** [remove_field_info t label] removes all the information
    about the field label in the record t. *)

(* Operations on substitutions and type variables *)

module type Subst = sig
    include Subst
    val compose : t -> t -> t (* compose s1 s2 does s2 \circ s1 *)
    val combine : t -> t -> t
    val split : t -> TVarSet.t -> t * t
end
module Subst : Subst
val instantiate : Subst.t list -> typ -> typ
val fresh_subst : TVarSet.t -> TVarSet.t * Subst.t
val fresh : TVarSet.t -> typ -> TVarSet.t * Subst.t * typ
val tallying : TVarSet.t (* Monomorphic *) -> (typ * typ) list -> Subst.t list
val tallying_infer : TVarSet.t (* Polymorphic *) -> TVarSet.t (* Non-inferred *) -> (typ * typ) list -> Subst.t list
val subtype_poly : TVarSet.t -> typ -> typ -> bool

(* Operations on jokers (legacy) *)

module Joker : sig
    type joker_kind = Min | Max
    val reserved_name_for_joker : joker_kind -> string

    val joker : joker_kind -> typ
    val jokers : joker_kind -> typ -> TVarSet.t
    val top_jokers : joker_kind -> typ -> TVarSet.t

    val substitute_jokers : joker_kind -> typ -> typ -> typ
    val substitute_all_jokers : typ -> typ -> typ
    val optimal : typ -> typ
    val worst : typ -> typ
    val substitute_top_jokers : joker_kind -> typ -> typ -> typ

    val decompose_branches : (typ*typ) list -> ((typ*typ) list) (* Jokerized branches *) * ((typ*typ) list)
    val share_jokerized_arrows : typ list -> typ list
end