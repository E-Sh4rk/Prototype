open Parsing.IO
open Common
open Types.Base
open Types.Additions
open Parsing
open Parsing.Variable
open Types.Tvar

type def = Variable.t * Ast.annot_expr * typ option

type typecheck_result =
| TSuccess of typ * Env.t * (float * float)
| TFailure of (Position.t list) * string

exception IncompatibleType of typ
let type_check_def tenv env (var,expr,typ_annot) =
  let time0 = Unix.gettimeofday () in
  let nf_expr = Msc.convert_to_msc expr in
  let time1 = Unix.gettimeofday () in
  try
    Utils.log "%a@." Poly.Msc.pp_e nf_expr ;
    let typ = Poly.Checker.typeof_simple tenv env nf_expr in
    let typ =
      match typ_annot with
      | None -> typ
      | Some typ' ->
        if subtype_poly typ typ'
        then
          let g = generalize (vars typ') in
          Subst.apply g typ'
        else raise (IncompatibleType typ)
    in
    let time2 = Unix.gettimeofday () in
    let msc_time = (time1 -. time0 ) *. 1000. in
    let typ_time = (time2 -. time1) *. 1000. in
    let env = Env.add var typ env in
    TSuccess (typ, env, (msc_time, typ_time))
  with
  | Poly.Checker.Untypeable (pos, str) -> TFailure (pos, str)
  | IncompatibleType _ ->
    TFailure (Variable.get_locations var,
      "the type inferred is not a subtype of the type specified")

type parsing_result =
| PSuccess of type_env * ((int * def) list)
| PFailure of Position.t * string

let parse_and_resolve f =
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
        let var = Variable.create ~binding:false (Some name) in
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
      List.fold_left treat_elem (empty_tenv, Ast.empty_name_var_map, []) ast in
    PSuccess (tenv, List.rev defs)
  with
    | Ast.LexicalError(pos, msg) -> PFailure (pos, msg)
    | Ast.SyntaxError (pos, msg) -> PFailure (pos, msg)
    | Ast.SymbolError msg -> PFailure (!last_pos, msg)
    | TypeDefinitionError msg -> PFailure (!last_pos, msg)
