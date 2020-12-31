open IO
open Nf_ast
open Types_additions
open Variable

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

let print_result str =
  Format.printf "%s@?" str

let type_check_program
  (program:Ast.parser_program) (pr:string -> unit) pr_logs pr_ill_typed =
  let test_def (tenv,varm,env) (name,parsed_expr) =
    Format.ksprintf pr "%s: " name;
    begin try
        let var = Variable.create (Some name) in
        let annot_expr = Ast.parser_expr_to_annot_expr tenv varm parsed_expr in
        let time = Unix.gettimeofday () in
        let nf_expr = convert_to_normal_form annot_expr in
        assert (VarSet.subset (fv_e nf_expr) (Env.domain env |> VarSet.of_list)) ;
        (*Format.printf "%a\n" pp_e nf_expr ;*)
        let typ = Checker.typeof_simple tenv env nf_expr in
        let time = (Unix.gettimeofday ()) -. time in
        let varm = StrMap.add name var varm in
        let env = Env.add var typ env in
        Format.ksprintf pr "%s (checked in %fs)\n" (Cduce.string_of_type typ) time;
        pr_logs () ; (varm, env)
      with Checker.Ill_typed (pos, str) ->
        pr_ill_typed (pos, str); (varm,env)
      end
    in
    let treat_elem (tenv,varm,env) elem =
      match elem with
      | Ast.Definition d ->
        let (varm,env) = test_def (tenv,varm,env) d in
        (tenv,varm,env)
      | Ast.Atoms lst ->
        let tenv = List.fold_left define_atom tenv lst in
        (tenv,varm,env)
      | Ast.Types lst ->
        let tenv = define_types tenv lst in
        (tenv,varm,env)
    in
    ignore (List.fold_left treat_elem (empty_tenv, Ast.empty_name_var_map, Env.empty) program)

let _ =
    (*Printexc.record_backtrace true;*)
    let fn = ref "test.ml" in
    if Array.length Sys.argv > 1 then fn := Sys.argv.(1) ;
    try
      type_check_program (parse_program_file !fn) print_result print_logs print_ill_typed
    with e ->
      let msg = Printexc.to_string e
      and stack = Printexc.get_backtrace () in
      Printf.eprintf "Uncatched exception: %s%s\n" msg stack
