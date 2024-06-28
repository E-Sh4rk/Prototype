open Main

let () =
    (* Printexc.record_backtrace true; *)
    if Unix.isatty Unix.stdout then Colors.add_ansi_marking Format.std_formatter ;
    try
        let fn = ref "test.ml" in
        if Array.length Sys.argv > 1 then fn := Sys.argv.(1) ;
        match parse_and_resolve (`File !fn) initial_varm with
        | PSuccess (tenv, lst) ->
            let time0 = Unix.gettimeofday () in
            List.fold_left (fun env (ll, (v, e, ta)) ->
                Utils.log_level := ll ;
                Format.printf "@{<blue;bold>%s@}: %!"
                    (Parsing.Variable.Variable.get_name v |> Option.get) ;
                match type_check_def tenv env (v,e,ta) with
                | TSuccess (t, env, time) ->
                    Format.printf "%s @{<italic;yellow>(checked in %.00fms)@}\n%!"
                        (Types.Tvar.string_of_type_short t) time ;
                    env
                | TFailure (_, msg, time) ->
                    Format.printf "@{<red>%s@} @{<italic;purple>(failed in %.00fms)@}\n%!" msg time ;
                    env
            ) initial_env lst |> ignore ;
            let time1 = Unix.gettimeofday () in
            Format.printf "@.@{<bold;green>Total time: %.02fs@}@." (time1 -. time0)
        | PFailure (pos, msg) ->
            Format.printf "@{<bold;red>%s: %s@}@." (Position.string_of_pos pos) msg
    with e ->
        let msg = Printexc.to_string e
        and stack = Printexc.get_backtrace () in
        Format.printf "@.Uncaught exception: %s\n%s@." msg stack
