%{ (* Emacs, use -*- tuareg -*- to open this file. *)

  open Ast
  open Types.Additions

  let annot sp ep e =
    (Ast.new_annot (Position.lex_join sp ep), e)

  let tmp_var = "__gen__"
  let multi_param_abstraction startpos endpos lst t =
    let step acc (annotation, pat) =
      match pat with
      | PatVar v -> annot startpos endpos (Lambda (annotation, v, acc))
      | pat ->
        let test = annot startpos endpos (Var tmp_var) in
        let body = annot startpos endpos (PatMatch (test, [(pat, acc)])) in
        annot startpos endpos (Lambda (annotation, tmp_var, body))
    in
    List.rev lst |> List.fold_left step t

  let double_app startpos endpos f a b =
    let app1 = annot startpos endpos (App (f, a)) in
    annot startpos endpos (App (app1, b))

  let rec list_of_elts startpos endpos = function
    | [] -> annot startpos endpos (Const Nil)
    | x::xs ->
    let left = x in let right = list_of_elts startpos endpos xs in
    annot startpos endpos (Pair (left,right))

  let rec record_update startpos endpos base = function
    | [] -> base
    | (label,e)::fields ->
      let base = annot startpos endpos (RecordUpdate (base, label, Some e)) in
      record_update startpos endpos base fields

%}

%token EOF
%token FUN LET IN FST SND DEBUG
%token IF IS THEN ELSE
%token LPAREN RPAREN EQUAL COMMA COLON INTERROGATION_MARK
%token ARROW AND OR NEG DIFF
%token ANY EMPTY BOOL CHAR (*FLOAT*) INT TRUE FALSE UNIT NIL STRING LIST
%token DOUBLEDASH TIMES PLUS MINUS DIV
%token LBRACE RBRACE DOUBLEPOINT MATCH WITH END EQUAL_OPT POINT LT GT
%token ATOMS TYPE TYPE_AND DOUBLE_OR (*DOUBLE_AND*)
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
%nonassoc DIFF
%nonassoc NEG

%%

program: e=element* EOF { e }

unique_term: t=term EOF { t }

element:
  i=optional_debug a=toplevel_definition { Definition (i, a) }
| ATOMS a=ID* { Atoms a }
| TYPE ts=separated_nonempty_list(TYPE_AND, param_type_def) { Types ts }

%inline optional_debug:
  { Utils.log_disabled }
| DEBUG {Utils.log_full}
| DEBUG i=lint { i }

%inline param_type_def: name=TID params=list(TVAR) EQUAL t=typ { (name, params, t) }

%inline toplevel_definition:
  LET i=toplevel_identifier ais=parameter* ty=optional_type_annot EQUAL t=term
  {
    let t = multi_param_abstraction $startpos $endpos ais t in
    (i, t, ty)
  }

%inline optional_type_annot:
    { None }
  | COLON t=typ { Some t }

(* ===== TERMS ===== *)

%inline definition:
  d=toplevel_definition { d }
  (* TODO: case of a single pattern *)

%inline optional_test_type:
  { TBase TTrue }
| IS t=typ { t }

term:
  t=simple_term { t }
  (* Explicitely annotated lambdas are not supported anymore *)
| FUN ais=parameter+ ARROW t = term { multi_param_abstraction $startpos $endpos ais t }
| d=definition IN t=term { annot $startpos $endpos (Let (Utils.fst3 d, Utils.snd3 d, t)) }
| IF t=term ott=optional_test_type THEN t1=term ELSE t2=term { annot $startpos $endpos (Ite (t,ott,t1,t2)) }
| MATCH t=term WITH pats=patterns END { annot $startpos $endpos (PatMatch (t,pats)) }
| lhs=simple_term COMMA rhs=term { annot $startpos $endpos (Pair (lhs, rhs)) }

simple_term:
  a=atomic_term { a }
| a=simple_term b=atomic_term { annot $startpos $endpos (App (a, b)) }
| FST a=atomic_term { annot $startpos $endpos (Projection (Fst, a)) }
| SND a=atomic_term { annot $startpos $endpos (Projection (Snd, a)) }
| a=atomic_term s=infix_term b=atomic_term { double_app $startpos $endpos s a b }
| p=prefix_term a=atomic_term { annot $startpos $endpos (App (p, a)) }
| a=atomic_term POINT id=toplevel_identifier { annot $startpos $endpos (Projection (Field id, a)) }
| a=atomic_term DIFF id=toplevel_identifier { annot $startpos $endpos (RecordUpdate (a,id,None)) }
| LT t=typ GT { annot $startpos $endpos (Abstract t) }

infix_term:
  x=infix { annot $startpos $endpos (Var x) }

prefix_term:
  x=prefix { annot $startpos $endpos (Var x) }

atomic_term:
  x=toplevel_identifier { annot $startpos $endpos (Var x) }
| l=literal { annot $startpos $endpos (Const l) }
| MAGIC { annot $startpos $endpos (Abstract (TBase TEmpty)) }
| LPAREN RPAREN { annot $startpos $endpos (Const Unit) }
| LPAREN t=term RPAREN { t }
| LBRACE obr=optional_base_record fs=separated_nonempty_list(COMMA, field_term) RBRACE
{ record_update $startpos $endpos obr fs }
| LBRACKET lst=separated_list(SEMICOLON, term) RBRACKET
{ list_of_elts $startpos $endpos lst }
| LPAREN t=term COLON ty=typ RPAREN { annot $startpos $endpos (TypeConstr (t,ty)) }

%inline optional_base_record:
  { annot $startpos $endpos (Const EmptyRecord) }
| a=atomic_term WITH { a }

%inline field_term:
  id=toplevel_identifier EQUAL t=simple_term { (id, t) }

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

parameter:
  arg = ID { (Unnanoted, PatVar arg) }
| LPAREN arg = pattern opta = optional_param_type_annot RPAREN
{ (opta, arg) }

%inline optional_param_type_annot:
    { Unnanoted }
  | COLON tys = separated_nonempty_list(SEMICOLON, typ) { ADomain tys }

toplevel_identifier:
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

(* ===== TYPES ===== *)

typ:
  t=simple_typ { t }
| lhs=simple_typ COMMA rhs=typ { TPair (lhs, rhs) }

simple_typ:
  t=atomic_typ { t }
| s=TID ts=nonempty_list(atomic_typ) { TCustom(ts, s) }
| lhs=simple_typ ARROW rhs=simple_typ { TArrow (lhs, rhs) }
| NEG t=simple_typ { TNeg t }
| lhs=simple_typ OR rhs=simple_typ  { TCup (lhs, rhs) }
| lhs=simple_typ AND rhs=simple_typ { TCap (lhs, rhs) }
| lhs=simple_typ DIFF rhs=simple_typ  { TDiff (lhs, rhs) }

atomic_typ:
  x=type_constant { TBase x }
| s=TID { TCustom ([], s) }
| s=TVAR { TVar s }
| LPAREN RPAREN { TBase TUnit }
| LPAREN t=typ RPAREN { t }
| LBRACE fs=separated_list(COMMA, typ_field) o=optional_open RBRACE { TRecord (o, fs) }
| LBRACKET re=typ_re RBRACKET { TSList re }

%inline optional_open:
  { false }
| DOUBLEPOINT { true }

%inline typ_field:
  id=toplevel_identifier EQUAL t=simple_typ { (id, t, false) }
| id=toplevel_identifier EQUAL_OPT t=simple_typ { (id, t, true) }

%inline type_constant:
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

%inline type_interval:
  lb=lint DOUBLEDASH ub=lint { TInt (Some lb, Some ub) }
| LPAREN DOUBLEDASH ub=lint RPAREN { TInt (None, Some ub) }
| LPAREN lb=lint DOUBLEDASH RPAREN { TInt (Some lb, None) }
| LPAREN DOUBLEDASH RPAREN { TInt (None, None) }

(* ===== REGEX ===== *)

typ_re:
  { ReEpsilon }
| re=simple_re { re }
| lhs=typ_re SEMICOLON rhs=simple_re { ReSeq (lhs, rhs) }

simple_re:
  re=atomic_re { re }
| lhs=simple_re DOUBLE_OR rhs=atomic_re { ReAlt (lhs, rhs) }

%inline strict_re:
| lhs=typ_re SEMICOLON rhs=simple_re { ReSeq (lhs, rhs) }
| lhs=simple_re DOUBLE_OR rhs=atomic_re { ReAlt (lhs, rhs) }

atomic_re:
  t=typ { ReType t }
| LPAREN re=strict_re RPAREN { re }
| re=atomic_re TIMES { ReStar re }
| re=atomic_re PLUS { ReSeq (re, ReStar re) }
| re=atomic_re INTERROGATION_MARK { ReAlt (re, ReEpsilon) }

(* ===== PATTERNS ===== *)

%inline patterns:
  lst=separated_nonempty_list(OR, pat_line) {lst}
| OR lst=separated_nonempty_list(OR, pat_line) {lst}

%inline pat_line:
  p=pattern ARROW t=term { (p,t) }

pattern:
  p=simple_pattern { p }
| lhs=simple_pattern COMMA rhs=pattern { PatPair (lhs, rhs) }

simple_pattern:
  p=atomic_pattern { p }
| lhs=simple_pattern AND rhs=atomic_pattern { PatAnd (lhs, rhs) }
| lhs=simple_pattern OR rhs=atomic_pattern { PatOr (lhs, rhs) }
| v=ID EQUAL t=simple_term { PatAssign (v, t) }

atomic_pattern:
  COLON t=atomic_typ { PatType t }
| v=ID  { PatVar v }
| LPAREN RPAREN { PatType (TBase TUnit) }
| LPAREN p=pattern RPAREN { p }
