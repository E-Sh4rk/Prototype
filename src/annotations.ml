type 'a annot_a' =
  | EmptyAtomA
  | UntypAtomA
  | AppA of Cduce.typ * bool
  | LambdaA of 'a
  [@@deriving show]

type ('a, 'b) annot' =
  | EmptyA
  | UntypA
  | BindA of ('a annot_a' * 'b)
  [@@deriving show]

module rec LambdaSA : sig
  type t
  val empty : unit -> t
  val destruct : t -> Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ)
  val add : t -> Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ) -> t
  val construct : (Cduce.typ * ((t,BindSA.t) annot' * Cduce.typ)) list -> t
  val map_top : (Cduce.typ -> Cduce.typ) -> t -> t
  val enrich : t -> (Cduce.typ * Cduce.typ) list -> t
  val pp : Format.formatter -> t -> unit
end = struct
  type t = T of (Cduce.typ * ((t, BindSA.t) annot' * Cduce.typ)) list
  [@@deriving show]
  let empty () = T []
  let destruct = failwith "TODO"
  let add = failwith "TODO"
  let construct = failwith "TODO"
  let map_top = failwith "TODO"
  let enrich = failwith "TODO"
end

and BindSA : sig
  type t
  val empty : unit -> t
  val destruct : t -> Cduce.typ * (t,BindSA.t) annot'
  val add : t -> Cduce.typ * (t,BindSA.t) annot' -> t
  val construct : (Cduce.typ * (t,BindSA.t) annot') list -> t
  val map_top : (Cduce.typ -> Cduce.typ) -> t -> t
  val splits : t -> Cduce.typ list
  val dom : t -> Cduce.typ
  val pp : Format.formatter -> t -> unit
end = struct
  type t = T of (Cduce.typ * (LambdaSA.t, t) annot') list
  [@@deriving show]
  let empty () = T []
  let destruct = failwith "TODO"
  let add = failwith "TODO"
  let construct = failwith "TODO"
  let map_top = failwith "TODO"
  let splits = failwith "TODO"
  let dom = failwith "TODO"
end

type annot_a = LambdaSA.t annot_a'
[@@deriving show]
type annot = (LambdaSA.t, BindSA.t) annot'
[@@deriving show]
