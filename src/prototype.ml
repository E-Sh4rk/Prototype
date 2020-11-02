open IO
open Nf_ast
open Types_additions

let print_logs () =
  (*let treat (exprid, data)  =
    if data.visited = 0 && data.ignored > 0
    then Utils.warning data.position "Expression is unreachable!"
  in
  Seq.iter treat (all_logs ()) ;
  clear_logs ()*)
  ()

let print_ill_typed (pos, str) =
  Format.printf "Ill typed\n" ; Utils.error pos str

let type_check_program
  (program:Ast.parser_program) (pr:string -> unit) pr_logs pr_ill_typed =
  let test_def (tenv,idm,varm,env) (name,parsed_expr) =
    Format.ksprintf pr "%s: " name;
    begin try
        let id = Ast.unique_varid () in
        let annot_expr = Ast.parser_expr_to_annot_expr tenv idm parsed_expr in
        let time = Unix.gettimeofday () in
        let var = Variable.create (Some name) in
        let nf_expr = convert_to_normal_form varm annot_expr in
        let typ = Checker.typeof tenv env nf_expr in
        let time = (Unix.gettimeofday ()) -. time in
        let idm = StrMap.add name id idm in
        let varm = Ast.ExprMap.add ((), Var id) var varm in
        let env = Checker.add_to_env var typ env in
        Format.ksprintf pr "%s (checked in %fs)\n" (Cduce.string_of_type typ) time;
        pr_logs () ; (idm, varm, env)
      with Checker.Ill_typed (pos, str) ->
        pr_ill_typed (pos, str); (idm,varm,env)
      end
    in
    let treat_elem (tenv,idm,varm,env) elem =
      match elem with
      | Ast.Definition d ->
        let (idm,varm,env) = test_def (tenv,idm,varm,env) d in
        (tenv,idm,varm,env)
      | Ast.Atoms lst ->
        let tenv = List.fold_left define_atom tenv lst in
        (tenv,idm,varm,env)
      | Ast.Types lst ->
        let tenv = define_types tenv lst in
        (tenv,idm,varm,env)
    in
    ignore (List.fold_left treat_elem (empty_tenv, Ast.empty_id_map, Ast.ExprMap.empty, Checker.empty_env) program)

let _ =
    let fn = ref "test.ml" in
    if Array.length Sys.argv > 1 then fn := Sys.argv.(1) ;
    type_check_program (parse_program_file !fn) print_string print_logs print_ill_typed