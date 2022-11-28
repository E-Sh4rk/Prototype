open Legacy
open Types.Base
open Types.Tvar
open Parsing.Variable
open Common.Msc
open Common

let v1 = Variable.create ~binding:true (Some "v1")
let v2 = Variable.create ~binding:true (Some "v2")

let%test "propagate-app" [@tags "no-js"] =
  let ii = mk_arrow (cons int_typ) (cons int_typ) in
  let aa = mk_arrow any_node any_node in
  let f = cap ii aa in
  let env = Env.singleton v1 f |> Env.add v2 any |> Ref_env.from_env in
  let e = App (v1, v2) in
  let (res, _) = Checker_poly.propagate_a env TVarSet.empty e any int_typ in
  match res with
  | [env] when equiv int_typ (Ref_env.find v2 env) -> true
  | _ -> false

let%test "neg_ref" [@tags "no-js"] =
  let b = Env.singleton v1 any |> Env.add v2 bool_typ |> Ref_env.from_env in
  let r = b |> Ref_env.push |> Ref_env.strengthen v2 true_typ in
  let res = Ref_env.neg_ref r in
  match res with
  | [renv] when Ref_env.find v1 renv |> equiv (any)
    && Ref_env.find v2 renv |> equiv (false_typ) -> true
  | _ -> false

let%test "neg_refs" [@tags "no-js"] =
  let b = Env.singleton v1 any |> Env.add v2 bool_typ |> Ref_env.from_env in
  let r1 = b |> Ref_env.push |> Ref_env.strengthen v1 int_typ
    |> Ref_env.strengthen v2 true_typ in
  let r2 = b |> Ref_env.push |> Ref_env.strengthen v2 false_typ in
  let res = Ref_env.neg_refs b [r1;r2] in
  match res with
  | [renv] when Ref_env.find v1 renv |> equiv (neg int_typ)
    && Ref_env.find v2 renv |> equiv (true_typ) -> true
  | _ -> false

let%test "tallying" [@tags "no-js"] =
  let u = TVar.mk_unregistered () in
  let input = TVar.mk_unregistered () in
  let output = TVar.mk_unregistered () in
  let poly1 = TVar.mk_unregistered () in
  let poly2 = TVar.mk_unregistered () in
  let right_udef = mk_arrow (TVar.typ input |> cons) (TVar.typ output |> cons) in
  let udef = mk_arrow (TVar.typ u |> cons) (cap right_udef (TVar.typ poly1) |> cons) in
  let udef = cap udef (TVar.typ poly2) in
  let ut = Raw.rectype udef u in
  let poly3 = (*mk_var "p3"*)poly1 in
  let poly4 = (*mk_var "p4"*)poly2 in
  let ut' = Subst.apply ([poly1, TVar.typ poly3; poly2, TVar.typ poly4] |> Subst.construct) ut in
  let res = TVar.mk_unregistered () |> TVar.typ in
  let left_part = mk_arrow (cons ut) (cons res) in
  let right_part = mk_arrow (cons ut') (cons res) in
  let res2 = TVar.mk_unregistered () in
  let right_part = mk_arrow (cons right_part) (res2 |> TVar.typ |> cons) in
  Format.printf "%a@.%a@." pp_typ left_part pp_typ right_part ;
  let constr = [left_part, right_part] in
  let poly = [poly1;poly2;poly3;poly4;res2] in
  let sol = Raw.tallying_raw ~var_order:poly TVarSet.empty constr in
  Format.printf "Number of solutions: %i@." (List.length sol) ;
  sol |> List.for_all (fun s ->
    subtype (Subst.apply s left_part) (Subst.apply s right_part)
  )

let%test "tallying2" [@tags "no-js"] =
  let av = TVar.mk_unregistered () in
  let xv = TVar.mk_unregistered () in
  let resv = TVar.mk_unregistered () in
  let left_part = mk_times (TVar.typ av |> cons) any_node in
  let left_part = mk_arrow (cons left_part) (TVar.typ av |> cons) in
  let right_part = mk_arrow (TVar.typ xv |> cons) (TVar.typ resv |> cons) in
  Format.printf "%a@.%a@." pp_typ left_part pp_typ right_part ;
  let constr = [left_part, right_part] in
  let sol = Raw.tallying_raw ~var_order:[resv;av] TVarSet.empty constr in
  Format.printf "Number of solutions: %i@." (List.length sol) ;
  sol |> List.for_all (fun s ->
    Format.printf "%a@." Subst.pp s ;
    subtype (Subst.apply s left_part) (Subst.apply s right_part)
  )

let%test "tallying3" [@tags "no-js"] =
  let av = TVar.mk_unregistered () in
  let xv = TVar.mk_unregistered () in
  let sxv = TVar.mk_unregistered () in
  let resv = TVar.mk_unregistered () in
  let left_part = mk_times (TVar.typ av |> cons) any_node in
  let left_part = mk_arrow (cons left_part) (TVar.typ av |> cons) in
  let right_part = cap (mk_times any_node (TVar.typ sxv |> cons)) (TVar.typ xv) in
  let right_part = mk_arrow (cons right_part) (TVar.typ resv |> cons) in
  Format.printf "%a@.%a@." pp_typ left_part pp_typ right_part ;
  let constr = [left_part, right_part] in
  let sol = Raw.tallying_raw ~var_order:[resv;av] (TVarSet.construct [sxv]) constr in
  Format.printf "Number of solutions: %i@." (List.length sol) ;
  sol |> List.for_all (fun s ->
    Format.printf "%a@." Subst.pp s ;
    subtype (Subst.apply s left_part) (Subst.apply s right_part)
  )
