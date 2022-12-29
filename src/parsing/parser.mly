%{ (* Emacs, use -*- tuareg -*- to open this file. *)

  open Ast
  open Types.Additions

  let parsing_error pos msg =
    raise (SyntaxError (Position.string_of_pos pos, msg))

  let var_or_primitive = function
    | x -> Var x

  let rec tuple pos = function
    | [] -> (Ast.new_annot pos, Const Unit)
    | [x] -> x
    | x::xs ->
    let left = x in let right = tuple pos xs in
    let pos_left = Ast.position_of_expr left in
    let pos_right = Ast.position_of_expr right in
    (Ast.new_annot (Position.join pos_left pos_right), Pair (left,right))

  let rec pattern_tuple = function
    | [] -> PatType (TBase TUnit)
    | [x] -> x
    | x::xs ->
    let left = x in let right = pattern_tuple xs in
    PatPair (left,right)

  let rec product = function
    | [] -> TBase TUnit
    | [t] -> t
    | t::ts ->
    let left = t in let right = product ts in
    TPair (left, right)

  let rec list_of_elts pos = function
    | [] -> (Ast.new_annot pos, Const Nil)
    | x::xs ->
    let left = x in let right = list_of_elts pos xs in
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

  let multi_param_abstraction startpos endpos lst t =
    List.rev lst |> List.fold_left (
      fun acc (annotation, v) ->
        annot startpos endpos (Lambda (annotation, v, acc))
    ) t

%}

%token EOF
%token FUN LET IN FST SND DEBUG
%token IF IS THEN ELSE
%token LPAREN RPAREN EQUAL COMMA COLON INTERROGATION_MARK
%token ARROW AND OR NEG DIFF
%token ANY EMPTY BOOL CHAR (*FLOAT*) INT TRUE FALSE UNIT NIL STRING LIST
%token DOUBLEDASH TIMES PLUS MINUS DIV
%token LBRACE RBRACE DOUBLEPOINT MATCH WITH END EQUAL_OPT POINT LT GT
%token ATOMS TYPE TYPE_AND DOUBLE_OR DOUBLE_AND
%token LBRACKET RBRACKET SEMICOLON
%token<string> ID
%token<string> TID
%token<string> TVAR
(*%token<float> LFLOAT*)
%token<int> LINT
%token<bool> LBOOL
%token<char> LCHAR
%token<string> LSTRING
%token LUNIT LNIL
%token MAGIC
%token<string> INFIX PREFIX

%type<Ast.parser_expr> term
%start<Ast.parser_expr> unique_term
%start<Ast.parser_program> program

%right ARROW
%left OR
%left AND
(*%left PLUS MINUS
%left TIMES DIV*)
%nonassoc DIFF
%nonassoc NEG

%%

program: e=element* EOF { e }
| error {
  parsing_error (Position.lex_join $startpos $endpos) "Syntax error."
}

unique_term: t=term EOF { t }
| error {
  parsing_error (Position.lex_join $startpos $endpos) "Syntax error."
}

element:
  a=definition { Definition (Utils.log_disabled, a) }
| DEBUG a=definition { Definition (Utils.log_full, a) }
| DEBUG i=LINT a=definition { Definition (i, a) }
| a=atoms      { Atoms a }
| a=types_def  { Types a }

atoms: ATOMS a=ID* { a }

types_def: TYPE ts=separated_nonempty_list(TYPE_AND, param_type_def) { ts }

param_type_def: name=TID params=list(TVAR) EQUAL t=typ { (name, params, t) }

term:
  a=abstraction { a }
| d=definition IN t=term { annot $startpos $endpos (Let (Utils.fst3 d, Utils.snd3 d, t)) }
(*| lhs=term b=binop rhs=term { App (App (Primitive b, lhs), rhs) }*)
| t=simple_term { t }
| IF t=term IS ty=typ THEN t1=term ELSE t2=term { annot $startpos $endpos (Ite (t,ty,t1,t2)) }
| IF t=term THEN t1=term ELSE t2=term { annot $startpos $endpos (Ite (t,TBase TTrue,t1,t2)) }
| MATCH t=term WITH pats=patterns END
| MATCH t=term WITH OR pats=patterns END
{ annot $startpos $endpos (PatMatch (t,pats)) }

simple_term:
  a=simple_term b=atomic_term { annot $startpos $endpos (App (a, b)) }
| FST a=atomic_term { annot $startpos $endpos (Projection (Fst, a)) }
| SND a=atomic_term { annot $startpos $endpos (Projection (Snd, a)) }
| a=atomic_term s=infix_term b=atomic_term
{ let app1 = annot $startpos $endpos (App (s, a)) in
  annot $startpos $endpos (App (app1, b)) }
| p=prefix_term a=atomic_term { annot $startpos $endpos (App (p, a)) }
| a=atomic_term POINT id=identifier { annot $startpos $endpos (Projection (Field id, a)) }
| a=atomic_term DIFF id=identifier { annot $startpos $endpos (RecordUpdate (a,id,None)) }
| LT t=typ GT { annot $startpos $endpos (Abstract t) }
(*| m=MINUS t=atomic_term { App (Primitive Neg, t) }*)
| a=atomic_term { a }

field_term:
  id=identifier EQUAL t=(*simple_term*)term { (id, t) }

infix_term:
  x=infix { annot $startpos $endpos (var_or_primitive x) }

prefix_term:
  x=prefix { annot $startpos $endpos (var_or_primitive x) }

atomic_term:
  x=identifier { annot $startpos $endpos (var_or_primitive x) }
| l=literal { annot $startpos $endpos (Const l) }
| MAGIC { annot $startpos $endpos (Abstract (TBase TEmpty)) }
| LBRACE fs=separated_list(COMMA, field_term) RBRACE
{ record_update (annot $startpos $endpos (Const EmptyRecord)) fs }
| LPAREN ts=separated_list(COMMA, term) RPAREN
{ tuple (Position.lex_join $startpos $endpos) ts }
| LBRACE a=atomic_term WITH fs=separated_nonempty_list(COMMA, field_term) RBRACE
{ record_update a fs }
| LBRACKET lst=separated_list(SEMICOLON, term) RBRACKET
{ list_of_elts (Position.lex_join $startpos $endpos) lst }
| LPAREN t=term COLON ty=typ RPAREN { annot $startpos $endpos (TypeConstr (t,ty)) }

literal:
(*f=LFLOAT { Float f }*)
  i=lint   { Int i }
| c=LCHAR  { Char c }
| b=LBOOL  { Bool b }
| s=LSTRING{ String s }
| LUNIT    { Unit }
| LNIL     { Nil }

lint:
| i=LINT { i }
| LPAREN PLUS i=LINT RPAREN { i }
| LPAREN MINUS i=LINT RPAREN { -i }

%inline abstraction:
  FUN LPAREN ty=typ RPAREN hd=identifier tl=annoted_identifier* ARROW t=term
{
  let t = multi_param_abstraction $startpos $endpos tl t in
  annot $startpos $endpos (Lambda (AArrow ty, hd, t))
}
| FUN ais=annoted_identifier+ ARROW t = term
{
  multi_param_abstraction $startpos $endpos ais t
}

%inline annoted_identifier:
  arg = identifier { (Unnanoted, arg) }
| LPAREN arg = identifier COLON tys = separated_nonempty_list(SEMICOLON, typ) RPAREN
{ (ADomain tys, arg) }

%inline definition:
  LET i=identifier ais=annoted_identifier* ty=optional_type_annot EQUAL t=term
  {
    let t = multi_param_abstraction $startpos $endpos ais t in
    (i, t, ty)
  }

%inline optional_type_annot:
    { None }
  | COLON t=typ { Some t }

(*%inline binop :
| PLUS  { Add }
| TIMES { Mul }*)

identifier:
  | x=ID | LPAREN x=prefix RPAREN | LPAREN x=infix RPAREN { x }

infix:
  | x=INFIX {x}
  | DIV   {"/"}
  | TIMES {"*"}
  | PLUS  {"+"}
  | MINUS {"-"}
  | EQUAL {"="}
  | LT    {"<"}
  | GT    {">"}

prefix:
  | x=PREFIX {x}
  | INTERROGATION_MARK {"?"}

typ:
  t=atomic_typ { t }
| s=TID ts=nonempty_list(atomic_typ) { TCustom(ts, s) }
| lhs=typ ARROW rhs=typ { TArrow (lhs, rhs) }
| NEG t=typ { TNeg t }
| lhs=typ OR rhs=typ  { TCup (lhs, rhs) }
| lhs=typ AND rhs=typ { TCap (lhs, rhs) }
| lhs=typ DIFF rhs=typ  { TDiff (lhs, rhs) }

atomic_typ:
  x=type_constant { TBase x }
| s=TID { TCustom ([], s) }
| s=TVAR { TVar s }
| LPAREN ts=separated_list(COMMA, typ) RPAREN { product ts }
| LBRACE fs=separated_list(COMMA, typ_field) RBRACE { TRecord (false, fs) }
| LBRACE fs=separated_list(COMMA, typ_field) DOUBLEPOINT RBRACE { TRecord (true, fs) }
| LBRACKET re=typ_re RBRACKET { TSList re }

typ_field:
  id=identifier EQUAL t=typ { (id, t, false) }
| id=identifier EQUAL_OPT t=typ { (id, t, true) }

type_constant:
(*  FLOAT { TyFloat }*)
  INT { TInt (None, None) }
| i=lint { TInt (Some i, Some i) }
| i=type_interval { i }
| CHAR { TChar }
| c=LCHAR { TSChar c }
| BOOL { TBool }
| TRUE { TTrue }
| FALSE { TFalse }
| UNIT { TUnit }
| EMPTY { TEmpty }
| ANY { TAny }
| NIL { TNil }
| STRING { TString }
| LIST { TList }
| str=LSTRING { TSString str }

type_interval:
(*  LBRACKET lb=lint SEMICOLON ub=lint RBRACKET { TInt (Some lb, Some ub) }
| LBRACKET SEMICOLON ub=lint RBRACKET { TInt (None, Some ub) }
| LBRACKET lb=lint SEMICOLON RBRACKET { TInt (Some lb, None) }
| LBRACKET SEMICOLON RBRACKET { TInt (None, None) }*)
  lb=lint DOUBLEDASH ub=lint { TInt (Some lb, Some ub) }
| COLON DOUBLEDASH ub=lint { TInt (None, Some ub) }
| lb=lint DOUBLEDASH COLON { TInt (Some lb, None) }
| COLON DOUBLEDASH COLON { TInt (None, None) }

(*%inline annoted(X): x=X {
  (Position.with_poss $startpos $endpos (unique_exprid ()), x)
}*)

typ_re:
  re=seq_re { re }
| re=simple_re { re }
| { ReEpsilon }
(* rs=separated_list(SEMICOLON, simple_re)
{ List.fold_left (fun acc r -> ReSeq (acc, r)) ReEpsilon rs }*)

seq_re:
  lhs=typ_re SEMICOLON rhs=simple_re { ReSeq (lhs, rhs) }

simple_re:
  re=atomic_re { re }
| re=alt_re { re }

alt_re:
  lhs=simple_re DOUBLE_OR rhs=atomic_re { ReAlt (lhs, rhs) }

atomic_re:
  t=typ { ReType t }
| LPAREN re=alt_re RPAREN { re }
| LPAREN re=seq_re RPAREN { re }
| re=atomic_re TIMES { ReStar re }
| re=atomic_re PLUS { ReSeq (re, ReStar re) }
| re=atomic_re INTERROGATION_MARK { ReAlt (re, ReEpsilon) }

pattern:
  p=atomic_pattern {p}
| lhs=pattern AND rhs=atomic_pattern { PatAnd (lhs, rhs) }
| lhs=pattern OR rhs=atomic_pattern { PatOr (lhs, rhs) }

atomic_pattern:
  COLON t=atomic_typ { PatType t }
| v=ID  { PatVar v }
| LPAREN ps=separated_list(COMMA, pattern) RPAREN
{ pattern_tuple ps }
| v=ID EQUAL l=literal (* TODO: It seems restrictive! *)
{ PatAssign (v, l) }

pat_line:
  p=pattern ARROW t=(*simple_term*)term { (p,t) }

patterns:
  lst=separated_nonempty_list(OR, pat_line) {lst}
