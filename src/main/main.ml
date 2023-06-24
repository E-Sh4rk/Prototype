open Parsing.IO
open System
open Types.Base
open Types.Additions
open Parsing
open Parsing.Variable
open Types.Tvar

type def = Variable.t * Ast.annot_expr * typ option

type typecheck_result =
| TSuccess of typ * Env.t * (float * float)
| TFailure of (Position.t list) * string * (float * float)

let generalize_all reduce t =
  let t = Subst.apply (generalize (vars t)) t |> bot_instance |> simplify_typ in
  if reduce then apply_subst_simplify (reduce_tvars t) t else t

exception IncompatibleType of typ
let type_check_def tenv env (var,expr,typ_annot) =
  let time0 = Unix.gettimeofday () in
  let (expr, addition) = Msc.remove_patterns_and_fixpoints expr in
  let nf_expr = Msc.convert_to_msc expr in
  let nf_addition = addition |> List.map (fun (v,e) -> v, Msc.convert_to_msc e) in
  let time1 = Unix.gettimeofday () in
  let retrieve_times () =
    let time2 = Unix.gettimeofday () in
    let msc_time = (time1 -. time0 ) *. 1000. in
    let typ_time = (time2 -. time1) *. 1000. in
    (msc_time, typ_time)
  in
  let type_additionnal env (v, nf) =
    let typ = Checker.typeof_simple tenv env nf |> generalize_all true in
    Env.add v typ env
  in
  try
    Utils.log "%a@." Msc.pp_e nf_expr ;
    let env = List.fold_left type_additionnal env nf_addition in
    let typ = Checker.typeof_simple tenv env nf_expr |> generalize_all true in
    let typ =
      match typ_annot with
      | None -> typ
      | Some typ' ->
        if subtype_poly typ typ'
        then typ' |> generalize_all false
        else raise (IncompatibleType typ)
    in
    let env = Env.add var typ env in
    TSuccess (typ, env, retrieve_times ())
  with
  | Checker.Untypeable (pos, str) ->
    TFailure (pos, str, retrieve_times ())
  | IncompatibleType _ ->
    TFailure (Variable.get_locations var,
      "the type inferred is not a subtype of the type specified",
      retrieve_times ())

type parsing_result =
| PSuccess of type_env * ((int * def) list)
| PFailure of Position.t * string

let builtin_functions =
  let arith_operators_typ =
    let int = cons int_typ in
    mk_arrow int (mk_arrow int int |> cons)
  in
  [
    ("+", arith_operators_typ) ;
    ("-", arith_operators_typ) ;
    ("*", arith_operators_typ) ;
    ("/", arith_operators_typ) ;
    ("%", arith_operators_typ)
  ]

let initial_varm =
  builtin_functions |> List.fold_left (fun varm (name, _) ->
    let var = Variable.create_other (Some name) in
    StrMap.add name var varm
  ) Ast.empty_name_var_map

let initial_env =
  builtin_functions |> List.fold_left (fun env (name, t) ->
    let var = StrMap.find name initial_varm in
    Env.add var t env
  ) Msc.initial_env

let parse_and_resolve f varm =
  let last_pos = ref Position.dummy in
  try
    let ast =
      match f with
        `File fn -> parse_program_file fn
      | `String s -> parse_program_string s
    in
    let treat_elem (tenv,varm,defs) (annot, elem) =
      last_pos := Position.position annot ;
      match elem with
      | Ast.Definition (log, (name, expr, tyo)) ->
        let tyo = match tyo with
        | None -> None
        | Some expr -> let (t, _) = type_expr_to_typ tenv empty_vtenv expr in Some t
        in
        let expr = Ast.parser_expr_to_annot_expr tenv empty_vtenv varm expr in
        let var = Variable.create_other (Some name) in
        Variable.attach_location var (Position.position annot) ;
        let varm = StrMap.add name var varm in
        (tenv,varm,(log,(var,expr,tyo))::defs)
      | Ast.Atoms lst ->
        let tenv = List.fold_left define_atom tenv lst in
        (tenv,varm,defs)
      | Ast.Types lst ->
        let (tenv, _) = define_types tenv empty_vtenv lst in
        (tenv,varm,defs)
    in
    let (tenv, _, defs) =
      List.fold_left treat_elem (empty_tenv, varm, []) ast in
    PSuccess (tenv, List.rev defs)
  with
    | Ast.LexicalError(pos, msg) -> PFailure (pos, msg)
    | Ast.SyntaxError (pos, msg) -> PFailure (pos, msg)
    | Ast.SymbolError msg -> PFailure (!last_pos, msg)
    | TypeDefinitionError msg -> PFailure (!last_pos, msg)
