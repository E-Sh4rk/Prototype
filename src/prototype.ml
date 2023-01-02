open Main

let () =
    Printexc.record_backtrace true;
    try
        let fn = ref "test.ml" in
        if Array.length Sys.argv > 1 then fn := Sys.argv.(1) ;
        match parse_and_resolve (`File !fn) with
        | PSuccess (tenv, lst) ->
            List.fold_left (fun env (ll, (v, e, ta)) ->
                Utils.log_level := ll ;
                Format.printf "%s: %!" (Parsing.Variable.Variable.get_name v |> Option.get) ;
                match type_check_def tenv env (v,e,ta) with
                | TSuccess (t, env, (tmsc, ttype)) ->
                    Format.printf "%s (checked in %.02fms (msc:%.02fms, type:%.02fms))\n%!" 
                        (Types.Tvar.string_of_type_short t) (tmsc +. ttype) tmsc ttype ;
                    env
                | TFailure (pos, msg) ->
                    Format.printf "Ill typed\n%!" ;
                    Utils.error Format.std_formatter pos msg ;
                    env
            ) Common.Env.empty lst |> ignore
        | PFailure (pos, msg) ->
            Format.printf "Error at pos %s: %s\n%!" (Position.string_of_pos pos) msg
    with e ->
        let msg = Printexc.to_string e
        and stack = Printexc.get_backtrace () in
        Format.printf "Uncaught exception: %s\n%s\n%!" msg stack
