{ (* Emacs, use -*- tuareg -*- to open this file. *)
  open Parser

  exception LexerError of string

  let enter_newline lexbuf =
    Lexing.new_line lexbuf;
    lexbuf
}

let newline = ('\010' | '\013' | "\013\010")

let blank   = [' ' '\009' '\012']

let id = ['a'-'z''_']['a'-'z''A'-'Z''0'-'9''_''\'']*

let type_id = ['A'-'Z']['a'-'z''A'-'Z''0'-'9''_''\'']*

let decimal = ['0'-'9']+ ('_'+ ['0'-'9']+)*

let int = decimal

let float_e = decimal ['e' 'E'] (['-' '+']? decimal)?
let float_comma = decimal '.' decimal (['e' 'E'] ['-' '+']? decimal)?
let float = (float_e | float_comma)

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
| "||"    { DOUBLE_OR }
(* | "&&"    { DOUBLE_AND } *)
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
| "match" { MATCH }
| "with"  { WITH }
| "end"   { END }
| "fun"   { FUN }
| "let"   { LET }
| "rec"   { REC }
| "in"    { IN }
| "fst"   { FST }
| "snd"   { SND }
| "debug" { DEBUG }
| "Any"   { ANY }
| "Empty" { EMPTY }
| "Bool"  { BOOL }
| "Char"  { CHAR }
| "Float" { FLOAT }
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
| float as f { LFLOAT (float_of_string f) }
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
| _ { raise (LexerError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

and comment depth = parse
| newline { enter_newline lexbuf |> comment depth }
| "*)" {
  if depth = 0 then token lexbuf else comment (depth - 1) lexbuf
}
| "(*" {
  comment (depth + 1) lexbuf
}
| eof { EOF }
| _ {
  comment depth lexbuf
}