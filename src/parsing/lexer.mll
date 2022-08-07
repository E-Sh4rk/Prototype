{ (* Emacs, use -*- tuareg -*- to open this file. *)
  open Parser

  let enter_newline lexbuf =
    Lexing.new_line lexbuf;
    lexbuf
}

let newline = ('\010' | '\013' | "\013\010")

let blank   = [' ' '\009' '\012']

let id = ['a'-'z']['a'-'z''A'-'Z''0'-'9''_']*

let type_id = ['A'-'Z']['a'-'z''A'-'Z''0'-'9''_']*

let decimal = ['0'-'9']+

let int = decimal

(*let fn = (int "." decimal?) | (int? "." decimal)*)

let type_var = '\'' ['a'-'z''A'-'Z''0'-'9''_']+

let char = '\'' ['a'-'z''A'-'Z''0'-'9''_'' ''-'] '\''

let string = '"' ['a'-'z''A'-'Z''0'-'9''_'' ''-']* '"'

let op_char =  '!' | '$' | '%' | '&' | '*' | '+' | '-' |
               '.' | '/' | ':' | ';' | '<' | '=' | '>' |
               '?' | '@' | '^' | '|' | '~'

let prefix_op = ('!' | '?') op_char*
let infix_op = ('=' | '<' | '>' | '@' | '^' | '|' | '&' |
                 '~' | '+' | '-' | '*' | '/' | '$' | '%') op_char*

rule token = parse
| newline { enter_newline lexbuf |> token }
| blank   { token lexbuf }
| "atoms" { ATOMS }
| "atom"  { ATOMS }
| "type"  { TYPE }
| "and"   { TYPE_AND }
| "or"    { REGEX_OR }
| "(*"    { comment 0 lexbuf }
| "->"    { ARROW }
| "&"     { AND }
| "|"     { OR }
| "\\"    { DIFF }
| "~"     { NEG  }
| ":"     { COLON }
| ","     { COMMA }
| "."     { POINT }
| "="     { EQUAL }
| "=?"    { EQUAL_OPT }
| "?"     { INTERROGATION_MARK }
| "if"    { IF }
| "is"    { IS }
| "then"  { THEN }
| "else"  { ELSE }
| "with"  { WITH }
| "fun"   { FUN }
| "let"   { LET }
| "in"    { IN }
| "fst"   { FST }
| "snd"   { SND }
| "debug" { DEBUG }
| "Any"   { ANY }
| "Empty" { EMPTY }
| "Bool"  { BOOL }
| "Char"  { CHAR }
(*| "Float" { FLOAT }*)
| "Int"   { INT }
| "Unit"  { UNIT }
| "True"  { TRUE }
| "False" { FALSE }
| "Nil"   { NIL }
| "String"{ STRING }
| "List"  { LIST }
| "("     { LPAREN }
| ")"     { RPAREN }
| "{"     { LBRACE }
| "}"     { RBRACE }
| "["     { LBRACKET }
| "]"     { RBRACKET }
| ";"     { SEMICOLON }
| "*"     { TIMES }
| "--"    { DOUBLEDASH }
| ".."    { DOUBLEPOINT }
| "-"     { MINUS }
| "+"     { PLUS  }
| "/"     { DIV   }
| "magic" { MAGIC }
| "<"     { LT }
| ">"     { GT }
| int as i { LINT (int_of_string i) }
(*| fn as f { LFLOAT (float_of_string f) }*)
| "true"  { LBOOL true }
| "false" { LBOOL false }
| "nil"   { LNIL }
| "unit"  { LUNIT }
| infix_op as s  { INFIX s }
| prefix_op as s { PREFIX s }
| string as s { LSTRING (String.sub s 1 ((String.length s) - 2)) }
| char as c { LCHAR (c.[1]) }
| id as s { ID s }
| type_id as s { TID s }
| type_var as s { TVAR (String.sub s 1 ((String.length s) - 1)) }
| eof     { EOF }
| _ as c  {
  raise (Ast.LexicalError (lexbuf.Lexing.lex_curr_pos,
      Printf.sprintf "Unexpected `%c'" c))
}

and comment depth = parse
| newline { enter_newline lexbuf |> comment depth }
| "*)" {
  if depth = 0 then token lexbuf else comment (depth - 1) lexbuf
}
| "(*" {
  comment (depth + 1) lexbuf
}
| eof {
    raise (Ast.LexicalError (lexbuf.Lexing.lex_curr_pos,
      "Unexecpted EOF inside comments."))
}
| _ {
  comment depth lexbuf
}