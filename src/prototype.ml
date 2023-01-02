let () =
    Printexc.record_backtrace true;
    let fn = ref "test.ml" in
    if Array.length Sys.argv > 1 then fn := Sys.argv.(1) ;
    try Main.main (`File !fn)
    with e ->
        let msg = Printexc.to_string e
        and stack = Printexc.get_backtrace () in
        Format.printf "Uncaught exception: %s%s\n%!" msg stack
  