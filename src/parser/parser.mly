%{
  open Input
%}

(* Infix operations *)
%token <Name.t * Location.t> QUESTIONMARK PREFIXOP EQ INFIXOP0 INFIXOP1 INFIXCONS INFIXOP2 STAR INFIXOP3 INFIXOP4

(* Names and numerals *)
%token UNDERSCORE
%token <Name.t> NAME
%token <int> NUMERAL

(* Parentheses & punctuations *)
%token LPAREN RPAREN
%token LBRACK RBRACK
%token LBRACE RBRACE
%token COLON COMMA PERIOD COLONGT COLONQT
%token ARROW DARROW

(* Modules *)
%token MODULE STRUCT

(* Things specific to toplevel *)
%token SEMISEMI
%token RULE

(* Let binding *)
%token LET REC AND IN

(* Dynamic variables *)
%token DYNAMIC NOW CURRENT

(* Meta-level programming *)
%token OPERATION
%token MATCH WHEN END
%token AS TYPE
%token VDASH EQEQ

%token HANDLE WITH HANDLER BAR VAL FINALLY YIELD
%token SEMI

%token NATURAL

%token EXTERNAL

%token UATOM

(* Meta types *)
%token MLUNIT MLSTRING
%token MLJUDGEMENT MLBOUNDARY
%token MLTYPE
%token MLFORALL
%token OF

(* References *)
%token BANG COLONEQ REF

(* Functions *)
%token FUNCTION

(* Assumptions *)
%token ASSUME CONVERT CONTEXT OCCURS

(* Toplevel directives *)
%token VERBOSITY
%token <string> QUOTED_STRING
%token REQUIRE INCLUDE OPEN

%token EOF

(* Precedence and fixity of infix operators *)
%nonassoc COLONEQ
%left     EQ INFIXOP0
%right    INFIXOP1
%right    INFIXCONS
%left     INFIXOP2
%left     STAR INFIXOP3
%right    INFIXOP4

%start <Input.toplevel list> file
%start <Input.toplevel> commandline

%%

(* Toplevel syntax *)

file:
  | ds=ml_module EOF                        { ds }

ml_module:
  |                                         { [] }
  | c=top_term                              { [c] }
  | c=top_term SEMISEMI cs=ml_module        { c :: cs }
  | c=top_command SEMISEMI cs=ml_module     { c :: cs }
  | c=top_command cs=ml_module_top          { c :: cs }

ml_module_top:
  |                                           { [] }
  | c=top_command SEMISEMI cs=ml_module       { c :: cs }
  | c=top_command cs=ml_module_top            { c :: cs }

commandline:
  | top_command SEMISEMI? EOF { $1 }
  | top_term SEMISEMI? EOF        { $1 }

(* Toplevel term *)
top_term: mark_location(plain_top_term) { $1 }
plain_top_term:
  | t=term { TopComputation t }

(* Toplevel commands that need not be preceeded by double semicolon. *)
top_command: mark_location(plain_top_command) { $1 }
plain_top_command:
  | REQUIRE mdls=separated_nonempty_list(COMMA, module_name)
                                                      { Require mdls }
  | INCLUDE mdl=long(module_name)                     { Include mdl }
  | OPEN mdl=long(module_name)                        { Open mdl }
  | MODULE mdl=module_name EQ STRUCT cmds=ml_module END
                                                      { TopModule (mdl, cmds) }
  | LET lst=separated_nonempty_list(AND, let_clause)  { TopLet lst }
  | LET REC lst=separated_nonempty_list(AND, recursive_clause)
                                                      { TopLetRec lst }
  | DYNAMIC x=ml_name u=dyn_annotation EQ c=term      { TopDynamic (x, u, c) }
  | NOW x=app_term EQ c=term                          { TopNow (x,c) }
  (* | HANDLE lst=top_handler_cases END                  { TopHandle lst } *)
  | MLTYPE lst=mlty_defs                              { DefMLType lst }
  | MLTYPE REC lst=mlty_defs                          { DefMLTypeRec lst }
  | OPERATION op=op_name COLON opsig=op_mlsig         { DeclOperation (op, opsig) }
  | VERBOSITY n=NUMERAL                               { Verbosity n }
  | EXTERNAL n=ml_name COLON sch=ml_schema EQ s=QUOTED_STRING
                                                      { DeclExternal (n, sch, s) }
  | RULE r=plain_rule                                 { r }

plain_rule:
  | c=tt_name ps=premises TYPE
    { RuleIsType (c, ps) }
  | c=tt_name ps=premises COLON ty=term
    { RuleIsTerm (c, ps, ty) }
  | c=tt_name ps=premises COLON l=app_term EQEQ r=ty_term
    { RuleEqType (c, ps, (l, r)) }
  | c=tt_name ps=premises COLON l=app_term EQEQ r=app_term COLON ty=term
    { RuleEqTerm (c, ps, (l, r, ty)) }

premises:
  |                                              { [] }
  | LPAREN p=premise RPAREN ps=premises          { p :: ps }

premise: mark_location(plain_premise) { $1 }
plain_premise:
  | lctx=local_context VDASH mv=opt_name(tt_name) TYPE             { PremiseIsType (mv, lctx) }
  | lctx=local_context VDASH mv=opt_name(tt_name) COLON ty=term    { PremiseIsTerm (mv, lctx, ty) }
  | lctx=local_context VDASH l=app_term EQEQ r=ty_term mv=equality_premise_name
    { PremiseEqType (mv, lctx, (l, r)) }
  | lctx=local_context VDASH l=app_term EQEQ r=app_term COLON ty=term mv=equality_premise_name
    { PremiseEqTerm (mv, lctx, (l, r, ty)) }

equality_premise_name:
  |                        { None }
  | AS x=opt_name(tt_name) { x }

local_context:
  |                                                           { []  }
  | x=anon_name(tt_name) COLON a=term                         { [(x, a)] }
  | x=anon_name(tt_name) COLON a=term COMMA ctx=local_context { (x, a) :: ctx }

(* Main syntax tree *)

term: mark_location(plain_term) { $1 }
plain_term:
  | e=plain_ty_term                                              { e }
  | LET a=separated_nonempty_list(AND,let_clause) IN c=term      { Let (a, c) }
  | LET REC lst=separated_nonempty_list(AND, recursive_clause) IN c=term
                                                                 { LetRec (lst, c) }
  | NOW x=app_term EQ c1=term IN c2=term                         { Now (x,c1,c2) }
  | CURRENT c=term                                               { Current c }
  | ASSUME x=opt_name(ml_name) COLON t=ty_term IN c=term         { Assume ((x, t), c) }
  | MATCH e=term WITH lst=match_cases END                        { Match (e, lst) }
  | HANDLE c=term WITH hcs=handler_cases END                     { Handle (c, hcs) }
  | FUNCTION xs=ml_arg+ DARROW e=term                            { Function (xs, e) }
  | WITH h=term HANDLE c=term                                    { With (h, c) }
  | HANDLER hcs=handler_cases END                                { Handler (hcs) }
  | e=app_term COLONQT bdry=ty_term                              { BoundaryAscribe (e, bdry) }
  | e=app_term COLON ty=ty_term                                  { TypeAscribe (e, ty) }
  | e1=binop_term SEMI e2=term                                   { Sequence (e1, e2) }
  | CONTEXT c=prefix_term                                        { Context c }
  | CONVERT c1=prefix_term c2=prefix_term                        { Convert (c1, c2) }
  | OCCURS c1=prefix_term c2=prefix_term                         { Occurs (c1, c2) }

ty_term: mark_location(plain_ty_term) { $1 }
plain_ty_term:
  | e=plain_binop_term                               { e }
  | a=abstraction e=binop_term                       { Abstract (a, e) }

binop_term: mark_location(plain_binop_term) { $1 }
plain_binop_term:
  | e=plain_app_term                                { e }
  | e1=app_term COLONEQ e2=binop_term               { Update (e1, e2) }
  | QUESTIONMARK TYPE                                            { MLBoundaryIsType }
  | QUESTIONMARK COLON t=app_term                                { MLBoundaryIsTerm t }
  | l=app_term EQEQ r=app_term AS QUESTIONMARK                   { MLBoundaryEqType (l, r) }
  | l=app_term EQEQ r=app_term COLON ty=term AS QUESTIONMARK     { MLBoundaryEqTerm (l, r, ty) }
  | e1=binop_term oploc=infix e2=binop_term
    { let (op, loc) = oploc in
      let op = Location.locate (Name (Name.PName op)) loc in
      Spine (op, [e1; e2])
    }

app_term: mark_location(plain_app_term) { $1 }
plain_app_term:
  | e=plain_prefix_term                             { e }
  | e=prefix_term s=substitution                    { Substitute (e, s) }
  | e=prefix_term es=nonempty_list(prefix_term)     { Spine (e, es) }

prefix_term: mark_location(plain_prefix_term) { $1 }
plain_prefix_term:
  | e=plain_simple_term                        { e }
  | REF e=prefix_term                          { Ref e }
  | BANG e=prefix_term                         { Lookup e }
  | oploc=prefix e2=prefix_term
    { let (op, loc) = oploc in
      let op = Location.locate (Name (Name.PName op)) loc in
      Spine (op, [e2])
    }
  | NATURAL t=prefix_term                      { Natural t }
  | YIELD e=prefix_term                        { Yield e }

(* simple_term: mark_location(plain_simple_term) { $1 } *)
plain_simple_term:
  | x=long(any_name)                                    { Name x }
  | s=QUOTED_STRING                                     { String s }
  | LBRACK lst=list_contents RBRACK                     { List lst }
  | LBRACK RBRACK                                       { List [] }
  | LPAREN c=term COLONGT t=ml_schema RPAREN            { MLAscribe (c, t) }
  | LPAREN lst=separated_list(COMMA, term) RPAREN       { match lst with
                                                          | [{Location.thing=e;loc=_}] -> e
                                                          | _ -> Tuple lst }

list_contents:
  | t=binop_term SEMI?                                 { [t] }
  | t=binop_term SEMI lst=list_contents                { t::lst }

(* ML variable name *)
ml_name:
  | NAME                     { $1 }
  | LPAREN op=infix RPAREN   { fst op }
  | LPAREN op=prefix RPAREN  { fst op }

(* ML operation name *)
op_name:
  | NAME                     { $1 }

(* ML module name *)
module_name:
  | NAME                     { $1 }

(* Type theory variable name *)
tt_name:
  | NAME                     { $1 }
  | LPAREN op=infix RPAREN   { fst op }
  | LPAREN op=prefix RPAREN  { fst op }

(* ML or type theory name *)
any_name:
  | tt_name                  { $1 }

(* ML constructor *)
constr_name:
  | NAME                     { $1 }
  | LPAREN op=infix RPAREN   { fst op }
  | LPAREN op=prefix RPAREN  { fst op }

module_path:
  | mdl=module_name                         { Name.PName mdl }
  | pth=module_path PERIOD mdl=module_name  { Name.PModule (pth, mdl) }

(* Possibly a name qualified with a module *)
%inline long(N):
  | x=N                              { Name.PName x }
  | pth=module_path PERIOD x=N       { Name.PModule (pth, x) }

(* Infix operators *)
%inline infix:
  | op=INFIXCONS   { op }
  | op=EQ          { op }
  | op=INFIXOP0    { op }
  | op=INFIXOP1    { op }
  | op=INFIXOP2    { op }
  | op=INFIXOP3    { op }
  | op=STAR        { op }
  | op=INFIXOP4    { op }

(* Prefix operators *)
%inline prefix:
  | op=PREFIXOP     { op }

(* A name or optionally _ *)
opt_name(X):
  | x=X             { Some x }
  | UNDERSCORE      { None }

(* A name or _, where _ is represented as an anonymous name *)
anon_name(X):
  | x=opt_name(X)   { match x with Some x -> x | None -> Name.anonymous () }

recursive_clause:
  | f=ml_name y=ml_arg ys=ml_arg* u=let_annotation EQ c=term
       { (f, y, ys, u, c) }

let_clause:
  | x=ml_name ys=ml_arg* u=let_annotation EQ c=term
       { Let_clause_ML (Some (x, ys), u, c) }
  | UNDERSCORE u=let_annotation EQ c=term
       { Let_clause_ML (None, u, c) }
  | x=ml_name COLON t=app_term EQ c=term
       { Let_clause_tt (Some x, t, c) }
  | UNDERSCORE COLON t=app_term EQ c=term
       { Let_clause_tt (None, t, c) }
  | pt=let_pattern u=let_annotation EQ c=term
       { Let_clause_patt (pt, u, c) }

(* A possibly annotated argument of an ML function *)
ml_arg:
  | x=ml_name                              { (x, Arg_annot_none) }
  | LPAREN x=ml_name COLONGT t=mlty RPAREN { (x, Arg_annot_ty t) }

let_annotation:
  |                       { Let_annot_none }
  | COLONGT sch=ml_schema { Let_annot_schema sch }

dyn_annotation:
  |                { Arg_annot_none }
  | COLONGT t=mlty { Arg_annot_ty t }

maybe_typed_binder:
  | LBRACE xs=anon_name(tt_name)+ RBRACE                     { List.map (fun x -> (x, None)) xs }
  | LBRACE xs=anon_name(tt_name)+ COLON t=ty_term RBRACE     { List.map (fun x -> (x, Some t)) xs }

abstraction:
  | lst=nonempty_list(maybe_typed_binder)          { List.concat lst }

substitution:
  | LBRACE subst=separated_nonempty_list(COMMA, term) RBRACE     { subst }

handler_cases:
  | BAR lst=separated_nonempty_list(BAR, handler_case)  { lst }
  | lst=separated_list(BAR, handler_case)               { lst }

handler_case:
  | VAL c=match_case DARROW t=term                                        { CaseVal c }
  | op=long(op_name) ps=prefix_pattern* pt=handler_checking DARROW t=term { CaseOp (op, (ps, pt, t)) }
  | FINALLY c=match_case                                                  { CaseFinally c }

handler_checking:
  |                     { None }
  | COLON pt=pattern { Some pt }

match_cases:
  | BAR lst=separated_nonempty_list(BAR, match_case)  { lst }
  | lst=separated_list(BAR, match_case)               { lst }

match_case:
  | p=pattern g=when_guard DARROW c=term  { (p, g, c) }

when_guard:
  |                    { None }
  | WHEN c=binop_term  { Some c }

(** Pattern matching *)

pattern: mark_location(plain_pattern) { $1 }
plain_pattern:
  | p=plain_binop_pattern                             { p }
  | p1=binop_pattern AS p2=binop_pattern              { Patt_As (p1, p2) }
  | p=binop_pattern TYPE                                           { Patt_IsType p }
  | p1=binop_pattern COLON p2=binop_pattern                     { Patt_IsTerm (p1, p2) }
  | p1=binop_pattern EQEQ  p2=binop_pattern                     { Patt_EqType (p1, p2) }
  | p1=binop_pattern EQEQ  p2=binop_pattern COLON p3=pattern { Patt_EqTerm (p1, p2, p3) }
  | abstr=tt_maybe_typed_binder p=pattern                    { Patt_Abstraction (abstr, p) }

binop_pattern: mark_location(plain_binop_pattern) { $1 }
plain_binop_pattern:
  | e=plain_app_pattern                                { e }
  | e1=binop_pattern oploc=infix e2=binop_pattern
    { let (op, _) = oploc in
      Patt_Constructor (Name.PName op, [e1; e2])
    }

(* app_pattern: mark_location(plain_app_pattern) { $1 } *)
plain_app_pattern:
  | e=plain_prefix_pattern                       { e }
  | t=long(any_name) ps=prefix_pattern+          { Patt_Constructor (t, ps) }

prefix_pattern: mark_location(plain_prefix_pattern) { $1 }
plain_prefix_pattern:
  | e=plain_simple_pattern           { e }
  | UATOM p=prefix_pattern        { Patt_GenAtom p }
  | oploc=prefix e=prefix_pattern
    { let (op, _) = oploc in
      Patt_Constructor (Name.PName op, [e])
    }

(* simple_pattern: mark_location(plain_simple_pattern) { $1 } *)
plain_simple_pattern:
  | UNDERSCORE                     { Patt_Anonymous }
  | x=long(ml_name)                { Patt_Path x }
  | LPAREN ps=separated_list(COMMA, pattern) RPAREN
    { match ps with
      | [{Location.thing=p;loc=_}] -> p
      | _ -> Patt_Tuple ps
    }
  | LBRACK ps=separated_list(SEMI, pattern) RBRACK { Patt_List ps }

let_pattern: mark_location(plain_let_pattern) { $1 }
plain_let_pattern:
  | LPAREN ps=separated_list(COMMA, pattern) RPAREN
    { match ps with
      | [{Location.thing=p;_}] -> p
      | _ -> Patt_Tuple ps
    }
  | LBRACK ps=separated_list(SEMI, pattern) RBRACK
    { Patt_List ps }

tt_maybe_typed_binder:
  | LBRACE xs=opt_name(tt_name)+ RBRACE                            { List.map (fun x -> (x, None)) xs }
  | LBRACE xs=opt_name(tt_name)+ COLON t=pattern RBRACE         { List.map (fun x -> (x, Some t)) xs }

(* ML types *)

op_mlsig:
  | lst=separated_nonempty_list(ARROW, prod_mlty)
    { match List.rev lst with
      | t :: ts -> (List.rev ts, t)
      | [] -> assert false
     }

ml_schema: mark_location(plain_ml_schema)  { $1 }
plain_ml_schema:
  | MLFORALL params=opt_name(ml_name)+ COMMA t=mlty { ML_Forall (params, t) }
  | t=mlty                                           { ML_Forall ([], t) }

mlty: mark_location(plain_mlty) { $1 }
plain_mlty:
  | plain_prod_mlty                  { $1 }
  | t1=prod_mlty ARROW t2=mlty       { ML_Arrow (t1, t2) }
  | t1=prod_mlty DARROW t2=mlty      { ML_Handler (t1, t2) }

prod_mlty: mark_location(plain_prod_mlty) { $1 }
plain_prod_mlty:
  | ts=separated_nonempty_list(STAR, app_mlty)
    { match ts with
      | [] -> assert false
      | [{Location.thing=t;loc=_}] -> t
      | _::_::_ -> ML_Prod ts
    }

app_mlty: mark_location(plain_app_mlty) { $1 }
plain_app_mlty:
  | plain_simple_mlty                                { $1 }
  | REF t=simple_mlty                                { ML_Ref t }
  | DYNAMIC t=simple_mlty                            { ML_Dynamic t }
  | c=long(ml_name) args=nonempty_list(simple_mlty) { ML_TyApply (c, args) }

simple_mlty: mark_location(plain_simple_mlty) { $1 }
plain_simple_mlty:
  | LPAREN t=plain_mlty RPAREN          { t }
  | c=long(ml_name)                     { ML_TyApply (c, []) }
  | MLJUDGEMENT                         { ML_Judgement }
  | MLBOUNDARY                          { ML_Boundary }
  | MLUNIT                              { ML_Prod [] }
  | MLSTRING                            { ML_String }
  | UNDERSCORE                          { ML_Anonymous }

mlty_defs:
  | lst=separated_nonempty_list(AND, mlty_def) { lst }

mlty_def:
  | a=ml_name xs=list(opt_name(ml_name)) EQ body=mlty_def_body { (a, (xs, body)) }

mlty_def_body:
  | t=mlty                                                           { ML_Alias t }
  | c=mlty_constructor BAR lst=separated_list(BAR, mlty_constructor) { ML_Sum (c :: lst) }
  | BAR lst=separated_list(BAR, mlty_constructor)                    { ML_Sum lst }

mlty_constructor:
  | c=constr_name OF lst=separated_nonempty_list(WITH, mlty)         { (c, lst) }
  | c=constr_name                                                    { (c, []) }

mark_location(X):
  x=X
  { Location.locate x (Location.make $startpos $endpos) }
%%
