open Types.Base
open Types.Tvar
open Types.Additions
open Parsing.Variable
open Msc
open Annotations

(* ====================================== *)
(* =============== TYPEOF =============== *)
(* ====================================== *)

exception Untypeable of Position.t list * string

let typeof_const_atom tenv c =
  match c with
  | Parsing.Ast.Atom str -> get_atom_type tenv str
  | c -> Parsing.Ast.const_to_typ c

let unbound_variable v =
  raise (Untypeable (Variable.get_locations v, "Unbound variable "^(Variable.show v)^"."))
  
let var_type v env =
  if Env.mem v env then Env.find v env else unbound_variable v

let instantiate_check pos ss t =
  let check_s s =
    Subst.dom s |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty
  in
  if List.for_all check_s ss
  then instantiate ss t
  else raise (Untypeable (pos, "Invalid instantiation: attempting to substitute a monomorphic variable."))

let check_mono pos t =
  if is_mono_typ t
  then ()
  else raise (Untypeable (pos, "Invalid type: lambda domains and splits should be monomorphic."))

let rename_check pos r t =
  if Subst.is_renaming r &&
    Subst.dom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty &&
    Subst.codom r |> TVarSet.filter TVar.is_mono |> TVarSet.is_empty
  then Subst.apply r t
  else raise (Untypeable (pos, "Invalid renaming."))

let typeof_inter typeof_branch pos branches =
  let untypeable str = raise (Untypeable (pos, str)) in
  if branches = []
  then untypeable ("Invalid intersection: there must be at least 1 branch.")
  else
    branches
    |> List.map (fun annot -> typeof_branch annot)
    |> conj_o

let cache c t = c.FullAnnot.typ <- Some t ; t

let rec typeof_a vardef tenv env (annot_a,c_a) a =
  let open FullAnnot in
  match c_a.typ with
  | Some t -> t
  | None ->
    let pos = Variable.get_locations vardef in
    let var_type v = var_type v env in
    let rename_check = rename_check pos in
    let instantiate_check = instantiate_check pos in
    let untypeable str = raise (Untypeable (pos, str)) in
    begin match a, annot_a with
    | a, InterA branches ->
      typeof_inter (fun annot_a -> typeof_a vardef tenv env annot_a a) pos branches
    | Alias v, AliasA -> var_type v
    | Const c, ConstA -> typeof_const_atom tenv c
    | Abstract t, AbstractA -> t
    | Pair (v1, v2), PairA (r1, r2) ->
      let t1 = var_type v1 |> rename_check r1 in
      let t2 = var_type v2 |> rename_check r2 in
      mk_times (cons t1) (cons t2)
    | Projection (Field label, v), ProjA ss ->
      let t = var_type v |> instantiate_check ss in
      if subtype t record_any
      then
        try get_field t label
        with Not_found ->
          untypeable ("Invalid projection: missing label " ^ label ^ ".")
      else untypeable ("Invalid projection: not a record.")
    | Projection (p, v), ProjA ss ->
      let t = var_type v |> instantiate_check ss in
      if subtype t pair_any
      then (if p = Fst then pi1 t else pi2 t)
      else untypeable ("Invalid projection: not a pair.")
    | RecordUpdate (v, label, None), RecordUpdateA (ss, None) ->
      let t = var_type v |> instantiate_check ss in
      if subtype t record_any
      then remove_field t label
      else untypeable ("Invalid field deletion: not a record.")
    | RecordUpdate (v, label, Some v'), RecordUpdateA (ss, Some r) ->
      let t = var_type v |> instantiate_check ss in
      if subtype t record_any
      then
        let t' = var_type v' |> rename_check r in
        let right_record = mk_record false [label, cons t'] in
        merge_records t right_record  
      else untypeable ("Invalid field update: not a record.")
    | TypeConstr (v, s), ConstrA ss ->
      let t = var_type v in
      if subtype (instantiate_check ss t) (disj s)
      then t
      else untypeable ("Type constraint not satisfied.")
    | TypeCoercion (v, s), CoercA ss ->
      let t = var_type v in
      let s = conj s in
      if subtype (instantiate_check ss t) s
      then s
      else untypeable ("Type coercion not possible.")
    | App (v1, v2), AppA (ss1, ss2) ->
      let apply t1 t2 =
        if subtype t1 arrow_any
        then
          if subtype t2 (domain t1)
          then apply t1 t2
          else untypeable ("Invalid application: argument not in the domain.")
        else untypeable ("Invalid application: not a function.")
      in
      (* NOTE: Approximation... this is not what the paper suggests,
        but given the inference we gain nothing by doing like in the paper. *)
      assert (List.length ss1 <> 0 && List.length ss2 <> 0) ;
      let treat_sigma (s1,s2) =
        let t1 = var_type v1 |> instantiate_check [s1] in
        let t2 = var_type v2 |> instantiate_check [s2] in
        apply t1 t2
      in
      List.combine ss1 ss2 |> List.map treat_sigma |> conj_o
      (* let t1 = var_type v1 |> instantiate_check ss1 in
      let t2 = var_type v2 |> instantiate_check ss2 in
      apply t1 t2 *)
    | Ite (v, _, _, _), EmptyA ss ->
      let t = var_type v |> instantiate_check ss in
      if is_empty t then empty
      else untypeable ("Invalid typecase: tested expression is not empty.")
    | Ite (v, s, v1, _), ThenA ss ->
      let t = var_type v |> instantiate_check ss in
      if subtype t s
      then var_type v1
      else untypeable ("Invalid typecase: tested expression hasn't the required type.")
    | Ite (v, s, _, v2), ElseA ss ->
      let t = var_type v |> instantiate_check ss in
      if subtype t (neg s)
      then var_type v2
      else untypeable ("Invalid typecase: tested expression hasn't the required type.")
    | Let (v1, v2), LetA ->
      if Env.mem v1 env
      then var_type v2
      else untypeable ("Invalid let binding: definition has not been typed.")
    | Lambda (_, v, e), LambdaA (s, annot) ->
      check_mono pos s ;
      let env = Env.add v s env in
      let t = typeof tenv env annot e in
      mk_arrow (cons s) (cons t)
    | _, _ -> untypeable ("Invalid annotations.")
    end
    |> bot_instance |> simplify_typ |> cache c_a

and typeof tenv env (annot,c) e =
  let open FullAnnot in
  match c.typ with
  | Some t -> t
  | None ->
    begin match e, annot with
    | e, Inter branches ->
      typeof_inter (fun annot -> typeof tenv env annot e) [] branches
    | Var v, BVar r -> var_type v env |> rename_check [] r
    | Bind (v, _, e), Skip annot ->
      assert (Env.mem v env |> not) ;
      typeof tenv env annot e
    | Bind (v, a, e), Keep (annot_a, splits, ss) ->
      let t = typeof_a v tenv env annot_a a in
      let pos = Variable.get_locations v in
      let untypeable str = raise (Untypeable (pos, str)) in
      if splits = []
      then untypeable ("Invalid decomposition: there must be at least 1 branch.")
      else
        let ti = t |> instantiate_check pos ss in
        if subtype ti (splits |> List.map fst |> disj)
        then
          splits |> List.map (fun (s, annot) ->
            check_mono pos s ;
            let env = Env.add v (cap t s) env in
            typeof tenv env annot e
          ) |> disj_o
        else untypeable ("Invalid decomposition: does not cover the type of the definition.")
    | _, _ -> raise (Untypeable ([], "Invalid annotations."))
    end
    |> bot_instance |> simplify_typ |> cache c

let typeof_a_nofail vardef tenv env annot_a a =
  try typeof_a vardef tenv env annot_a a
  with Untypeable (_, str) -> Format.printf "%a: %s@." pp_a a str ; assert false

let typeof_nofail tenv env annot e =
  try typeof tenv env annot e
  with Untypeable (_, str) -> Format.printf "%a: %s@." pp_e e str ; assert false  
