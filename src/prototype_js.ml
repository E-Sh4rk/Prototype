open Js_of_ocaml
open Main

let output = Dom_html.getElementById "output"
let button = Dom_html.getElementById "checkButton"
let textarea = Dom_html.getElementById_coerce "code" Dom_html.CoerceTo.textarea |> Option.get

let out_fun err =
  (fun s i l ->
    let s = String.sub s i l in
    let s = if err then
      "<span class='error'>" ^ s ^ "</span>"
    else s in
    output ##. innerHTML :=
    Js.string ((Js.to_string output##.innerHTML) ^ s);
  )

let ofmt = Format.make_formatter (out_fun false) ignore
let efmt = Format.make_formatter (out_fun true) ignore

let () =
  ignore @@
    Dom_html.addEventListener button Dom_html.Event.click
    (Dom_html.handler (fun _ ->
        output ##.innerHTML := Js.string "";
        let txt = textarea##.value in
        begin match parse_and_resolve (`String (Js.to_string txt)) with
        | PSuccess (tenv, lst) ->
            List.fold_left (fun env (_, (v, e, ta)) ->
                Format.fprintf ofmt "%s: %!" (Parsing.Variable.Variable.get_name v |> Option.get) ;
                match type_check_def tenv env (v,e,ta) with
                | TSuccess (t, env, (tmsc, ttype)) ->
                    Format.fprintf ofmt "%s (checked in %.02fms (msc:%.02fms, type:%.02fms))\n%!" 
                        (Types.Tvar.string_of_type_short t) (tmsc +. ttype) tmsc ttype ;
                    env
                | TFailure (pos, msg, _) ->
                    Format.fprintf efmt "Ill typed\n%!" ;
                    Utils.error efmt pos msg ;
                    env
            ) Common.Env.empty lst |> ignore
        | PFailure (pos, msg) ->
            Format.fprintf efmt "Error at pos %s: %s\n%!" (Position.string_of_pos pos) msg
        end ; Js._true)
  ) Js._false
