open Js_of_ocaml

let () =
  let output = Dom_html.getElementById "output" in
  let out_fun err =
    (fun s i l ->
      let s = String.sub s i l in
      let s = if err then
        "<span class='errror'>" ^ s ^ "</span>"
      else s in
      output ##. innerHTML :=
      Js.string ((Js.to_string output##.innerHTML) ^ s);
      )
    in
    let ofmt = Format.make_formatter (out_fun false) ignore in
    let efmt = Format.make_formatter (out_fun true) ignore in
    Main.std_fmt := ofmt;
    Main.err_fmt := efmt;
    let button = Dom_html.getElementById "checkButton" in
    ignore @@ 
     Dom_html.addEventListener button Dom_html.Event.click
     (Dom_html.handler (fun _ ->
         match Dom_html.getElementById_coerce "code" Dom_html.CoerceTo.textarea with
         None -> Js._true
         | Some textArea ->  let txt = textArea##.value in
           Main.main (`String (Js.to_string txt))
         ;  Js._true)
    ) Js._false
