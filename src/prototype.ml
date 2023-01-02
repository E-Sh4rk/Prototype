open Main

let print_ill_typed (pos, str) =
    Format.printf "Ill typed\n%!" ; Utils.error (Format.std_formatter) pos str
  
let print_result str =
    Format.printf "%s@?" str

let () =
    Printexc.record_backtrace true;
    try
        let fn = ref "test.ml" in
        if Array.length Sys.argv > 1 then fn := Sys.argv.(1) ;
        match parse_and_resolve (`File !fn)
        with
        | PSuccess (tenv, lst) ->
            List.fold_left (fun env (ll, def) ->
                Utils.log_level := ll ;
                type_check_def tenv env def print_result print_ill_typed
            ) Common.Env.empty lst |> ignore
        | PFailure (pos, msg) ->
            Format.printf "Error at pos %s: %s\n%!" (Position.string_of_pos pos) msg
    with e ->
        let msg = Printexc.to_string e
        and stack = Printexc.get_backtrace () in
        Format.printf "Uncaught exception: %s\n%s\n%!" msg stack
  