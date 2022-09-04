open Parsing.IO
open Common.Msc
open Common
open Types.Base
open Types.Additions
open Parsing
open Parsing.Variable

let std_fmt = ref Format.std_formatter
let err_fmt = ref Format.err_formatter

let print_ill_typed (pos, str) =
  Format.fprintf !std_fmt "Ill typed\n%!" ; Utils.error !std_fmt pos str

let print_result str =
  Format.fprintf !std_fmt "%s@?" str

let use_poly () = true
let compare_to_popl () = false

let type_check_program
  (program:Ast.parser_program) (pr:string -> unit) pr_ill_typed =
  let test_def (tenv,varm,env) (name,parsed_expr) =
    Format.ksprintf pr "%s: " name;
    begin
      let var = Variable.create (Some name) in
      let annot_expr = Ast.parser_expr_to_annot_expr tenv empty_vtenv varm parsed_expr in
      let time0 = Unix.gettimeofday () in
      let nf_expr = Msc.convert_to_msc annot_expr in
      let nf_expr_ann = nf_expr |> Legacy.Msc.from_common_msc ~legacy:true in
      let time1 = Unix.gettimeofday () in
      assert (VarSet.subset (fv_e nf_expr) (Env.domain env |> VarSet.of_list)) ;
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
          then Poly.Old_checker.typeof_simple tenv env TVarSet.empty nf_expr
          else Legacy.Checker.typeof_simple tenv env nf_expr_ann
        in
        let time2 = Unix.gettimeofday () in
        let msc_time = (time1 -. time0 ) *. 1000. in
        let typ_time = (time2 -. time1) *. 1000. in
        let time = (time2 -. time1) *. 1000. in
        let varm = StrMap.add name var varm in
        let env = Env.add var typ env in
        Format.ksprintf pr "%s (checked in %.02fms (msc:%.02fms, type:%.02fms))\n" 
          (string_of_type typ) time msc_time typ_time;
        if compare_to_popl () then
          begin match typ_legacy with
          | None -> Format.ksprintf pr "===== Good news: Was untypable with POPL22 system =====\n" 
          | Some t ->
            if subtype typ t |> not
            then (
              Format.ksprintf pr "===== Warning: Not better than the type obtained by POPL22 system =====\nType was: %s\n"
              (string_of_type t)
            )
          end ;
        (varm, env)
      end with Legacy.Checker.Ill_typed (pos, str)
      | Poly.Old_checker.Untypeable (pos, str) ->
        pr_ill_typed (pos, str);
        if compare_to_popl () then
          begin match typ_legacy with
          | None -> ()
          | Some t ->
            Format.ksprintf pr "===== Warning: Was typable with POPL22 system =====\nType was: %s\n" (string_of_type t)
          end ;
        (varm,env)
      end
    in
    let treat_elem (tenv,varm,env) elem =
      match elem with
      | Ast.Definition (log, d) ->
        Utils.log_level := log ;
        let (varm,env) = test_def (tenv,varm,env) d in
        (tenv,varm,env)
      | Ast.Atoms lst ->
        let tenv = List.fold_left define_atom tenv lst in
        (tenv,varm,env)
      | Ast.Types lst ->
        let (tenv, _) = define_types tenv empty_vtenv lst in
        (tenv,varm,env)
    in
    ignore (List.fold_left treat_elem (empty_tenv, Ast.empty_name_var_map, Env.empty) program)


let main f =
  Printexc.record_backtrace true;
  try
    let ast =
      match f with
        `File fn -> parse_program_file fn
      | `String s -> parse_program_string s
    in
    type_check_program ast print_result print_ill_typed
  with
    | Ast.LexicalError(pos, msg) ->
        Format.fprintf !err_fmt "Lexical error at position %d, %s\n%!" pos msg
    | Ast.SyntaxError (spos, msg) ->
       Format.fprintf !err_fmt "%s, %s\n%!" spos msg
    | Ast.UndefinedSymbol s ->
      Format.fprintf  !err_fmt "Error: undefined symbol `%s'\n%!" s
    | e ->
      let msg = Printexc.to_string e
      and stack = Printexc.get_backtrace () in
      Format.fprintf !err_fmt "Uncaught exception: %s%s\n%!" msg stack
