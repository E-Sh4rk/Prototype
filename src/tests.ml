open Cduce
open Variable
open Msc
open Types_additions

let v1 = Variable.create (Some "v1")
let v2 = Variable.create (Some "v2")

let%test "refine-app" [@tags "no-js"] =
  let ii = mk_arrow (cons int_typ) (cons int_typ) in
  let aa = mk_arrow any_node any_node in
  let f = cap ii aa in
  let env = Env.singleton v1 f |> Env.add v2 any |> Ref_env.from_env in
  let e = App (v1, v2) in
  let res = Checker_poly.refine_a empty_tenv env (varset []) e any int_typ in
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
