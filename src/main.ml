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

let std_fmt = ref Format.std_formatter
let err_fmt = ref Format.err_formatter

let print_ill_typed (pos, str) =
  Format.fprintf !std_fmt "Ill typed\n%!" ; Utils.error pos str

let print_result str =
  Format.fprintf !std_fmt "%s@?" str

let type_check_program
  (program:Ast.parser_program) (pr:string -> unit) pr_logs pr_ill_typed =
  let test_def (tenv,varm,env) (name,parsed_expr) =
    Format.ksprintf pr "%s: " name;
    begin
      let var = Variable.create (Some name) in
      let annot_expr = Ast.parser_expr_to_annot_expr tenv varm parsed_expr in
      let time0 = Unix.gettimeofday () in
      let nf_expr = convert_to_normal_form annot_expr in
      let time1 = Unix.gettimeofday () in
      assert (VarSet.subset (fv_e nf_expr) (Env.domain env |> VarSet.of_list)) ;
      try
        let typ = Checker.typeof_simple tenv env nf_expr in
        let time2 = Unix.gettimeofday () in
        let msc_time = (time1 -. time0 ) *. 1000. in
        let typ_time = (time2 -. time1) *. 1000. in
        let time = (time2 -. time1) *. 1000. in
        let varm = StrMap.add name var varm in
        let env = Env.add var typ env in
        Format.ksprintf pr "%s (checked in %.02fms (msc:%.02fms, type:%.02fms))\n" 
          (Cduce.string_of_type typ) time msc_time typ_time;
        pr_logs () ; (varm, env)
      with Checker.Ill_typed (pos, str) ->
        (*Format.printf "%a\n" pp_e nf_expr ;*)
        pr_ill_typed (pos, str); (varm,env)
      end
    in
    let treat_elem (tenv,varm,env) elem =
      match elem with
      | Ast.Definition (log, d) ->
        if log then Utils.log_enabled := true ;
        let (varm,env) = test_def (tenv,varm,env) d in
        Utils.log_enabled := false ;
        (tenv,varm,env)
      | Ast.Atoms lst ->
        let tenv = List.fold_left define_atom tenv lst in
        (tenv,varm,env)
      | Ast.Types lst ->
        let tenv = define_types tenv lst in
        (tenv,varm,env)
    in
    ignore (List.fold_left treat_elem (empty_tenv, Ast.empty_name_var_map, Env.empty) program)


let main f =
  let ast =
    match f with
      `File fn -> parse_program_file fn
    | `String s -> parse_program_string s
  in
    try
      type_check_program ast print_result print_logs print_ill_typed
    with e ->
      let msg = Printexc.to_string e
      and stack = Printexc.get_backtrace () in
      Format.fprintf !err_fmt "Uncaught exception: %s%s\n%!" msg stack
