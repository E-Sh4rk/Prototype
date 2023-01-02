open Main
open Js_of_ocaml
open Yojson.Basic

module Html = Dom_html

let json_of_pos pos =
  let open Position in
  let start = start_of_position pos in
  let endd = end_of_position pos in
  `Assoc [("startLine", `Int (line start)) ; ("startCol", `Int (column start)) ;
  ("endLine", `Int (line endd)) ; ("endCol", `Int (column endd))]

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
            let def_pos = Parsing.Variable.Variable.get_locations v in
            match type_check_def tenv env (v,e,ta) with
            | TSuccess (t, env, (tmsc, ttype)) ->
                let typ = Types.Tvar.string_of_type_short t in
                let time = tmsc +. ttype in
                let typ =
                  `Assoc [("name", `String name) ; ("def_pos", json_of_pos_list def_pos) ;
                  ("typeable", `Bool true) ; ("type", `String typ) ; ("time", `Float time)]
                in
                (env, typ::res)
            | TFailure (pos, msg) ->
              let untyp =
                `Assoc [("name", `String name) ; ("def_pos", json_of_pos_list def_pos) ;
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
  Js.export "typecheck"
    (object%js
       method typecheck code = typecheck code
     end)
