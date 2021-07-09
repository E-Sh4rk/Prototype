let () =
    let fn = ref "test.ml" in
    if Array.length Sys.argv > 1 then fn := Sys.argv.(1) ;
    Main.main (`File !fn)