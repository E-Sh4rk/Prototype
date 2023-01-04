open Main
open Js_of_ocaml
open Yojson.Basic

module Html = Dom_html

let json_of_pos pos =
  let open Position in
  let startp = start_of_position pos in
  let endp = end_of_position pos in
  `Assoc [("startLine", `Int (line startp)) ; ("startCol", `Int (column startp)) ;
  ("endLine", `Int (line endp)) ; ("endCol", `Int (column endp)) ;
  ("startOffset", `Int (offset startp)) ; ("endOffset", `Int (offset endp))]

let json_of_pos_list pos =
  `List (List.map json_of_pos pos)

let typecheck code =
  let res =
    try (
      match parse_and_resolve (`String (Js.to_string code)) with
      | PSuccess (tenv, lst) ->
        let (_, res) =
          List.fold_left (fun (env, res) (_, (v, e, ta)) ->
            let name = Parsing.Variable.Variable.get_name v |> Option.get in
            let def_pos = Parsing.Variable.Variable.get_locations v |> List.hd in
            match type_check_def tenv env (v,e,ta) with
            | TSuccess (t, env, (tmsc, ttype)) ->
                let typ = Types.Tvar.string_of_type_short t in
                let time = tmsc +. ttype in
                let typ =
                  `Assoc [("name", `String name) ; ("def_pos", json_of_pos def_pos) ;
                  ("typeable", `Bool true) ; ("type", `String typ) ; ("time", `Float time)]
                in
                (env, typ::res)
            | TFailure (pos, msg, (tmsc, ttype)) ->
              let time = tmsc +. ttype in
              let untyp =
                `Assoc [("name", `String name) ; ("def_pos", json_of_pos def_pos) ; ("time", `Float time) ;
                ("typeable", `Bool false) ; ("message", `String msg) ; ("pos", json_of_pos_list pos)]
              in
              (env, untyp::res)
          ) (Common.Env.empty, []) lst
        in
        `Assoc [("exit_code", `Int 0); ("results", `List (List.rev res))]
      | PFailure (pos, msg) ->
        `Assoc [("exit_code", `Int (-2)); ("message", `String msg); ("pos", json_of_pos_list [pos])]
    ) with _ ->
      `Assoc [("exit_code", `Int (-1)); ("message", `String ("internal error")); ("pos", `List [])]
  in
  Js.string (to_string res)

let _ =
  Js.export "checker"
    (object%js
       method typecheck code = typecheck code
     end)
