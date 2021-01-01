%{ (* Emacs, use -*- tuareg -*- to open this file. *)

  open Ast
  open Types_additions

  let parsing_error pos msg =
    Printf.eprintf "%s:\n  %s\n" (Position.string_of_pos pos) msg;
    exit 1

  let var_or_primitive = function
    | x -> Var x

  let rec tuple = function
    | [] -> assert false
    | [x] -> x
    | x::xs ->
    let left = x in let right = tuple xs in
    let pos_left = Ast.position_of_expr left in
    let pos_right = Ast.position_of_expr right in
    (Ast.new_annot (Position.join pos_left pos_right), Pair (left,right))

  let rec record_update base = function
    | [] -> base
    | (label,e)::fields ->
      let pos = Position.join (position_of_expr base) (position_of_expr e) in
      let base = (Ast.new_annot pos, RecordUpdate (base, label, Some e)) in
      record_update base fields

  let annot sp ep e =
    (Ast.new_annot (Position.lex_join sp ep), e)

%}

%token EOF
%token FUN LET IN FST SND DEBUG
%token IF IS THEN ELSE
%token LPAREN RPAREN EQUAL COMMA COLON
%token ARROW AND OR NEG DIFF
%token ANY EMPTY BOOL CHAR (*FLOAT*) INT TRUE FALSE UNIT
%token DOUBLEDASH TIMES (*PLUS MINUS*)
%token LBRACE RBRACE DOUBLEPOINT WITH EQUAL_OPT POINT
%token ATOMS TYPE TYPE_AND
(*%token LBRACKET RBRACKET SEMICOLON*)
%token<string> ID
%token<string> TID
(*%token<float> LFLOAT*)
%token<int> LINT
%token<bool> LBOOL
%token<char> LCHAR
%token<string> LSTRING
%token LUNIT
%token MAGIC

%type<Ast.parser_expr> term
%start<Ast.parser_expr> unique_term
%start<(Ast.varname * Ast.parser_expr) list> definitions
%start<Ast.parser_program> program

%right ARROW (*IN*)
%left OR
%left AND
(*%left PLUS*)
(*%left TIMES*)
%nonassoc DIFF
%nonassoc NEG

%%

program: e=element* EOF { e }
| error {
  parsing_error (Position.lex_join $startpos $endpos) "Syntax error."
}

definitions: a=definition* EOF { a }
| error {
  parsing_error (Position.lex_join $startpos $endpos) "Syntax error."
}

unique_term: t=term EOF { t }
| error {
  parsing_error (Position.lex_join $startpos $endpos) "Syntax error."
}


element:
  a=definition { Definition a }
| a=atoms      { Atoms a }
| a=types_def  { Types a }

atoms: ATOMS a=ID* { a }

types_def: TYPE ts=separated_nonempty_list(TYPE_AND, name_and_typ) { ts }

name_and_typ: name=TID EQUAL t=typ { (name, t) }

term:
  a=abstraction { a }
| d=definition IN t=term { annot $startpos $endpos (Let (fst d, snd d, t)) }
(*| lhs=term b=binop rhs=term { App (App (Primitive b, lhs), rhs) }*)
| t=simple_term { t }
| IF t=term IS ty=typ THEN t1=term ELSE t2=term { annot $startpos $endpos (Ite (t,ty,t1,t2)) }
| IF t=term THEN t1=term ELSE t2=term { annot $startpos $endpos (Ite (t,TBase TTrue,t1,t2)) }

simple_term:
  a=simple_term b=atomic_term { annot $startpos $endpos (App (a, b)) }
| FST a=atomic_term { annot $startpos $endpos (Projection (Fst, a)) }
| SND a=atomic_term { annot $startpos $endpos (Projection (Snd, a)) }
| a=atomic_term POINT id=identifier { annot $startpos $endpos (Projection (Field id, a)) }
| a=atomic_term DIFF id=identifier { annot $startpos $endpos (RecordUpdate (a,id,None)) }
| LBRACE a=simple_term WITH fs=separated_nonempty_list(COMMA, field_term) RBRACE { record_update a fs }
| DEBUG str=LSTRING a=atomic_term { annot $startpos $endpos (Debug (str, a)) }
(*| m=MINUS t=atomic_term { App (Primitive Neg, t) }*)
| a=atomic_term { a }

field_term:
  id=identifier EQUAL t=simple_term { (id, t) }

atomic_term:
  x=identifier { annot $startpos $endpos (var_or_primitive x) }
| l=literal { annot $startpos $endpos (Const l) }
| LBRACE fs=separated_list(COMMA, field_term) RBRACE
  { record_update (annot $startpos $endpos (Const EmptyRecord)) fs }
| LPAREN ts=separated_nonempty_list(COMMA, term) RPAREN { tuple ts }

literal:
(*f=LFLOAT { Float f }*)
  i=LINT   { Int i }
| c=LCHAR  { Char c }
| b=LBOOL  { Bool b }
| LUNIT    { Unit }
| MAGIC    { Magic }

%inline abstraction:
  FUN LPAREN ty=typ RPAREN vs=identifier+ ARROW t=term
{
  if List.length vs > 1 then failwith "Fun with multiple arguments not supported yet!"
  else annot $startpos $endpos (Lambda (AArrow ty, List.hd vs, t))
}
| FUN LPAREN arg = identifier COLON ty = typ RPAREN ARROW t = term
{
  annot $startpos $endpos (Lambda (ADomain ty, arg, t))
}
| FUN arg = identifier ARROW t = term
{
  annot $startpos $endpos (Lambda (Unnanoted, arg, t))
}

%inline definition: LET i=identifier EQUAL t=term
{
  (i, t)
}

(*%inline binop :
| PLUS  { Add }
| TIMES { Mul }*)

identifier: x=ID { x }

typ:
  x=type_constant { TBase x }
| s=TID { TCustom s }
| lhs=typ ARROW rhs=typ { TArrow (lhs, rhs) }
| LPAREN lhs=typ COMMA rhs=typ RPAREN { TPair (lhs, rhs) }
| NEG t=typ { TNeg t }
| lhs=typ AND rhs=typ { TCap (lhs, rhs) }
| lhs=typ OR rhs=typ  { TCup (lhs, rhs) }
| lhs=typ DIFF rhs=typ  { TDiff (lhs, rhs) }
| LBRACE fs=separated_list(COMMA, typ_field) RBRACE { TRecord (false, fs) }
| LBRACE fs=separated_list(COMMA, typ_field) DOUBLEPOINT RBRACE { TRecord (true, fs) }
| LPAREN t=typ RPAREN { t }

typ_field:
  id=identifier EQUAL t=typ { (id, t, false) }
| id=identifier EQUAL_OPT t=typ { (id, t, true) }

type_constant:
(*  FLOAT { TyFloat }*)
  INT { TInt (None, None) }
| i=LINT { TInt (Some i, Some i) }
| i=type_interval { i }
| CHAR { TChar }
| BOOL { TBool }
| TRUE { TTrue }
| FALSE { TFalse }
| UNIT { TUnit }
| EMPTY { TEmpty }
| ANY { TAny }

type_interval:
(*  LBRACKET lb=LINT SEMICOLON ub=LINT RBRACKET { TInt (Some lb, Some ub) }
| LBRACKET SEMICOLON ub=LINT RBRACKET { TInt (None, Some ub) }
| LBRACKET lb=LINT SEMICOLON RBRACKET { TInt (Some lb, None) }
| LBRACKET SEMICOLON RBRACKET { TInt (None, None) }*)
  lb=LINT DOUBLEDASH ub=LINT { TInt (Some lb, Some ub) }
| TIMES DOUBLEDASH ub=LINT { TInt (None, Some ub) }
| lb=LINT DOUBLEDASH TIMES { TInt (Some lb, None) }
| TIMES DOUBLEDASH TIMES { TInt (None, None) }

(*%inline annoted(X): x=X {
  (Position.with_poss $startpos $endpos (unique_exprid ()), x)
}*)
