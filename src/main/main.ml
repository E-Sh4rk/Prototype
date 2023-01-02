open Parsing.IO
open Common
open Types.Base
open Types.Additions
open Parsing
open Parsing.Variable
open Types.Tvar

let use_poly () = true
let compare_to_popl () = false

type def = Variable.t * Ast.annot_expr * typ option

(* TODO: refactor *)
exception IncompatibleType of typ
let type_check_def tenv env (var,annot_expr,typ_annot) (pr:string -> unit) pr_ill_typed =
  Format.ksprintf pr "%s: " (Variable.get_name var |> Option.get);
  begin
    let time0 = Unix.gettimeofday () in
    let nf_expr = Msc.convert_to_msc annot_expr in
    let nf_expr_ann = nf_expr |> Legacy.Msc.from_common_msc ~legacy:true in
    let time1 = Unix.gettimeofday () in
    let tmp_log = !Utils.log_level in
    Utils.log_level := Utils.log_disabled ;
    let typ_legacy =
      if compare_to_popl ()
      then
        try Some (Legacy.Old_checker.typeof_simple_legacy tenv env nf_expr_ann)
        with Legacy.Old_checker.Ill_typed _ -> None
      else None
    in
    Utils.log_level := tmp_log ;
    try begin
      Utils.log "%a@." Poly.Msc.pp_e nf_expr ;
      let typ =
        if use_poly ()
        then
          let typ = Poly.Checker.typeof_simple tenv env nf_expr in
          begin match typ_annot with
          | None -> typ
          | Some typ' ->
            if subtype_poly typ typ'
            then
              let g = generalize (vars typ') in
              Subst.apply g typ'
            else raise (IncompatibleType typ)
          end
        else Legacy.Checker.typeof_simple tenv env nf_expr_ann
      in
      let time2 = Unix.gettimeofday () in
      let msc_time = (time1 -. time0 ) *. 1000. in
      let typ_time = (time2 -. time1) *. 1000. in
      let time = (time2 -. time1) *. 1000. in
      let env = Env.add var typ env in
      Format.ksprintf pr "%s (checked in %.02fms (msc:%.02fms, type:%.02fms))\n" 
        (string_of_type_short typ) time msc_time typ_time;
      if compare_to_popl () then
        begin match typ_legacy with
        | None -> Format.ksprintf pr "===== Good news: Was untypable with POPL22 system =====\n" 
        | Some t ->
          if subtype typ t |> not
          then (
            Format.ksprintf pr "===== Warning: Not better than the type obtained by POPL22 system =====\nType was: %s\n"
            (string_of_type_short t)
          )
        end ;
      env
    end with Legacy.Checker.Ill_typed (pos, str)
    | Poly.Checker.Untypeable (pos, str) ->
      pr_ill_typed (pos, str);
      if compare_to_popl () then
        begin match typ_legacy with
        | None -> ()
        | Some t ->
          Format.ksprintf pr "===== Warning: Was typable with POPL22 system =====\nType was: %s\n" (string_of_type_short t)
        end ;
        env
      | IncompatibleType t ->
        Format.ksprintf pr "The type inferred is not a subtype of the provided annotation: %s\n" (string_of_type_short t) ;
        env
    end

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
