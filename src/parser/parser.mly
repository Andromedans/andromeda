%{
  open Input
%}

(* Type *)
%token TYPE

(* Products *)
%token PROD LAMBDA

(* Infix operations *)
%token <Name.ident * Location.t> PREFIXOP INFIXOP0 INFIXOP1 INFIXCONS INFIXOP2 STAR INFIXOP3 INFIXOP4

(* Equality types *)
%token EQEQ
%token REFL

(* Names and numerals *)
%token UNDERSCORE
%token <Name.ident> NAME
%token <int> NUMERAL

(* Parentheses & punctuations *)
%token LPAREN RPAREN
%token LBRACK RBRACK
%token COLON COMMA COLONGT
%token ARROW DARROW

(* Things specific to toplevel *)
%token DO FAIL
%token CONSTANT

(* Let binding *)
%token LET REC EQ AND IN

(* Dynamic variables *)
%token DYNAMIC NOW CURRENT

(* Meta-level programming *)
%token OPERATION
%token <Name.ident> PATTVAR
%token MATCH
%token AS
%token VDASH

%token HANDLE WITH HANDLER BAR VAL FINALLY END YIELD
%token SEMICOLON

%token CONGR_PROD CONGR_APPLY CONGR_LAMBDA CONGR_EQ CONGR_REFL
%token BETA_STEP

%token NATURAL

%token EXTERNAL

%token UATOM UCONSTANT

(* Meta types *)
%token JUDGMENT MLUNIT MLSTRING
%token MLTYPE
%token OF

(* REFERENCES *)
%token BANG COLONEQ REF

(* Functions *)
%token FUNCTION

(* Assumptions *)
%token ASSUME CONTEXT OCCURS

(* Substitution *)
%token WHERE

(* Toplevel directives *)
%token VERBOSITY
%token <string> QUOTED_STRING
%token REQUIRE

%token EOF

(* Precedence and fixity of infix operators *)
%nonassoc COLONEQ
%left     INFIXOP0
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
  | f=filecontents EOF            { f }

filecontents:
  |                                 { [] }
  | d=topcomp ds=filecontents       { d :: ds }
  | d=topdirective ds=filecontents  { d :: ds }

commandline:
  | topcomp EOF       { $1 }
  | topdirective EOF { $1 }

(* Things that can be defined on toplevel. *)
topcomp: mark_location(plain_topcomp) { $1 }
plain_topcomp:
  | LET lst=separated_nonempty_list(AND, let_clause)  { TopLet lst }
  | LET REC lst=separated_nonempty_list(AND, recursive_clause)
                                                      { TopLetRec lst }
  | DYNAMIC x=var_name u=dyn_annotation EQ c=term     { TopDynamic (x, u, c) }
  | NOW x=term EQ c=term                              { TopNow (x,c) }
  | HANDLE lst=top_handler_cases END                  { TopHandle lst }
  | DO c=term                                         { TopDo c }
  | FAIL c=term                                       { TopFail c }
  | CONSTANT xs=separated_nonempty_list(COMMA, var_name) COLON u=term
                                                      { DeclConstants (xs, u) }
  | MLTYPE lst=mlty_defs                              { DefMLType lst }
  | MLTYPE REC lst=mlty_defs                          { DefMLTypeRec lst }
  | OPERATION op=var_name COLON opsig=op_mlsig        { DeclOperation (op, opsig) }
  | VERBOSITY n=NUMERAL                               { Verbosity n }
  | EXTERNAL n=var_name COLON sch=ml_schema EQ s=QUOTED_STRING
                                                      { DeclExternal (n, sch, s) }

(* Toplevel directive. *)
topdirective: mark_location(plain_topdirective)      { $1 }
plain_topdirective:
  | REQUIRE fs=QUOTED_STRING+                        { Require fs }

(* Main syntax tree *)

term: mark_location(plain_term) { $1 }
plain_term:
  | e=plain_ty_term                                              { e }
  | LET a=separated_nonempty_list(AND,let_clause) IN c=term      { Let (a, c) }
  | LET REC lst=separated_nonempty_list(AND, recursive_clause) IN c=term
                                                                 { LetRec (lst, c) }
  | NOW x=term EQ c1=term IN c2=term                             { Now (x,c1,c2) }
  | CURRENT c=term                                               { Current c }
  | ASSUME x=var_name COLON t=ty_term IN c=term                  { Assume ((x, t), c) }
  | c1=equal_term WHERE e=simple_term EQ c2=term                 { Where (c1, e, c2) }
  | MATCH e=term WITH lst=match_cases END                        { Match (e, lst) }
  | HANDLE c=term WITH hcs=handler_cases END                     { Handle (c, hcs) }
  | WITH h=term HANDLE c=term                                    { With (h, c) }
  | HANDLER hcs=handler_cases END                                { Handler (hcs) }
  | e=app_term COLON t=ty_term                                   { Ascribe (e, t) }
  | e1=equal_term SEMICOLON e2=term                              { Sequence (e1, e2) }
  | CONTEXT c=prefix_term                                        { Context c }
  | OCCURS c1=prefix_term c2=prefix_term                         { Occurs (c1,c2) }

ty_term: mark_location(plain_ty_term) { $1 }
plain_ty_term:
  | e=plain_equal_term                               { e }
  | PROD a=prod_abstraction COMMA e=term             { Prod (a, e) }
  | LAMBDA a=lambda_abstraction COMMA e=term         { Lambda (a, e) }
  | FUNCTION xs=ml_arg+ DARROW e=term                { Function (xs, e) }
  | t1=equal_term ARROW t2=ty_term                   { Prod ([(Name.anonymous (), t1)], t2) }

equal_term: mark_location(plain_equal_term) { $1 }
plain_equal_term:
  | e=plain_binop_term                               { e }
  | e1=binop_term EQEQ e2=binop_term                 { Eq (e1, e2) }

binop_term: mark_location(plain_binop_term) { $1 }
plain_binop_term:
  | e=plain_app_term                                { e }
  | e1=app_term COLONEQ e2=binop_term               { Update (e1, e2) }
  | e2=binop_term oploc=infix e3=binop_term
    { let (op, loc) = oploc in
      let op = Location.locate (Var op) loc in
      Spine (op, [e2; e3])
    }

app_term: mark_location(plain_app_term) { $1 }
plain_app_term:
  | e=plain_prefix_term                             { e }
  | e=prefix_term es=nonempty_list(prefix_term)     { Spine (e, es) }
  | CONGR_PROD e1=prefix_term e2=prefix_term e3=prefix_term { CongrProd (e1, e2, e3) }
  | CONGR_APPLY e1=prefix_term e2=prefix_term e3=prefix_term e4=prefix_term e5=prefix_term
    { CongrApply (e1, e2, e3, e4, e5) }
  | CONGR_LAMBDA e1=prefix_term e2=prefix_term e3=prefix_term e4=prefix_term
    { CongrLambda (e1, e2, e3, e4) }
  | CONGR_EQ e1=prefix_term e2=prefix_term e3=prefix_term
    { CongrEq (e1, e2, e3) }
  | CONGR_REFL e1=prefix_term e2=prefix_term
    { CongrRefl (e1, e2) }
  | BETA_STEP e1=prefix_term e2=prefix_term e3=prefix_term e4=prefix_term e5=prefix_term
    { BetaStep (e1, e2, e3, e4, e5) }

prefix_term: mark_location(plain_prefix_term) { $1 }
plain_prefix_term:
  | e=plain_simple_term                        { e }
  | REF e=prefix_term                          { Ref e }
  | BANG e=prefix_term                         { Lookup e }
  | oploc=prefix e2=prefix_term
    { let (op, loc) = oploc in
      let op = Location.locate (Var op) loc in
      Spine (op, [e2])
    }
  | NATURAL t=prefix_term                      { Natural t }
  | YIELD e=prefix_term                        { Yield e }
  | REFL e=prefix_term                         { Refl e }

simple_term: mark_location(plain_simple_term) { $1 }
plain_simple_term:
  | TYPE                                                { Type }
  | x=var_name                                          { Var x }
  | s=QUOTED_STRING                                     { String s }
  | LBRACK lst=separated_list(COMMA, equal_term) RBRACK { List lst }
  | LPAREN c=term COLONGT t=ml_schema RPAREN            { MLAscribe (c, t) }
  | LPAREN lst=separated_list(COMMA, term) RPAREN       { match lst with
                                                          | [{Location.thing=e;loc=_}] -> e
                                                          | _ -> Tuple lst }

var_name:
  | NAME { $1 }
  | LPAREN op=infix RPAREN   { fst op }
  | LPAREN op=prefix RPAREN  { fst op }

%inline infix:
  | op=INFIXCONS   { op }
  | op=INFIXOP0    { op }
  | op=INFIXOP1    { op }
  | op=INFIXOP2    { op }
  | op=INFIXOP3    { op }
  | op=STAR        { op }
  | op=INFIXOP4    { op }

%inline prefix:
  | op=PREFIXOP { op }

name:
  | x=var_name { x }
  | UNDERSCORE { Name.anonymous () }

recursive_clause:
  | f=name y=ml_arg ys=ml_arg* u=let_annotation EQ c=term
       { (f, y, ys, u, c) }

let_clause:
  | x=name ys=ml_arg* u=let_annotation EQ c=term
       { Let_clause_ML (x, ys, u, c) }
  | x=name COLON t=ty_term EQ c=term
       { Let_clause_tt (x, t, c) }

ml_arg:
  | x=name                              { (x, Arg_annot_none) }
  | LPAREN x=NAME COLONGT t=mlty RPAREN { (x, Arg_annot_ty t) }

let_annotation:
  |                       { Let_annot_none }
  | COLONGT sch=ml_schema { Let_annot_schema sch }

dyn_annotation:
  |                { Arg_annot_none }
  | COLONGT t=mlty { Arg_annot_ty t }

typed_binder:
  | LPAREN xs=name+ COLON t=ty_term RPAREN         { List.map (fun x -> (x, t)) xs }

maybe_typed_binder:
  | x=name                                         { [(x, None)] }
  | LPAREN xs=name+ COLON t=ty_term RPAREN         { List.map (fun x -> (x, Some t)) xs }

prod_abstraction:
  | lst=nonempty_list(typed_binder)
    { List.concat lst }
  | lst=nonempty_list(name) COLON t=ty_term
    { List.map (fun x -> (x, t)) lst }

lambda_abstraction:
  | lam=raw_nonempty_lambda_abstraction { fst lam }

raw_nonempty_lambda_abstraction:
  | x=name lam=raw_lambda_abstraction
    { let (l,t) = lam in ((x,t)::l,t) }
  | xs=typed_binder ys=maybe_typed_binder*
    { ((List.map (fun (x,t) -> (x,Some t)) xs) @ (List.concat ys), None) }

raw_lambda_abstraction:
  | { ([],None) }
  | COLON t=ty_term { ([],Some t) }
  | x=name lam=raw_lambda_abstraction
    { let (l,t) = lam in ((x,t)::l,t) }
  | xs=typed_binder ys=maybe_typed_binder*
    { ((List.map (fun (x,t) -> (x,Some t)) xs) @ (List.concat ys), None) }

handler_cases:
  | BAR lst=separated_nonempty_list(BAR, handler_case)  { lst }
  | lst=separated_list(BAR, handler_case)               { lst }

handler_case:
  | VAL p=pattern DARROW t=term                                 { CaseVal (p, t) }
  | op=var_name ps=prefix_pattern* pt=handler_checking DARROW t=term                { CaseOp (op, (ps, pt, t)) }
  | oploc=prefix p=prefix_pattern pt=handler_checking DARROW t=term
      { let (op, _) = oploc in
        CaseOp (op, ([p], pt, t))
      }
  | p1=binop_pattern oploc=infix p2=binop_pattern pt=handler_checking DARROW t=term
    { let (op, _) = oploc in
      CaseOp (op, ([p1; p2], pt, t))
    }
  | FINALLY p=pattern DARROW t=term                             { CaseFinally (p, t) }

handler_checking:
  |                    { None }
  | COLON pt=pattern { Some pt }

top_handler_cases:
  | BAR lst=separated_nonempty_list(BAR, top_handler_case)  { lst }
  | lst=separated_list(BAR, top_handler_case)               { lst }

(* XXX allow patterns here *)
top_handler_case:
  | op=var_name xs=top_patt_maybe_var* y=top_handler_checking DARROW t=term
    { (op, (xs, y, t)) }
  | oploc=prefix x=top_patt_maybe_var y=top_handler_checking DARROW t=term
    { let (op, _) = oploc in
      (op, ([x], y, t))
    }
  | x1=top_patt_maybe_var oploc=infix x2=top_patt_maybe_var y=top_handler_checking DARROW t=term
    { let (op, _) = oploc in
      (op, ([x1;x2], y, t)) }

top_patt_maybe_var:
  | x=patt_var                   { Some x }
  | UNDERSCORE                   { None }

top_handler_checking:
  |                            { None }
  | COLON x=top_patt_maybe_var { x }

match_cases:
  | BAR lst=separated_nonempty_list(BAR, match_case)  { lst }
  | lst=separated_list(BAR, match_case)               { lst }

match_case:
  | p=pattern DARROW c=term  { (p, c) }

(** Pattern matching *)

pattern: mark_location(plain_pattern) { $1 }
plain_pattern:
  | p=plain_binop_pattern                   { p }
  | p=simple_pattern AS x=patt_var          { Patt_As (p,x) }
  | VDASH e1=tt_pattern COLON e2=tt_pattern { Patt_Jdg (e1, Some e2) }
  | VDASH e1=tt_pattern                     { Patt_Jdg (e1, None) }

binop_pattern: mark_location(plain_binop_pattern) { $1 }
plain_binop_pattern:
  | e=plain_app_pattern                                { e }
  | e1=binop_pattern oploc=infix e2=binop_pattern
    { let (op, _) = oploc in
      Patt_Constr (op, [e1; e2])
    }

(* app_pattern: mark_location(plain_app_pattern) { $1 } *)
plain_app_pattern:
  | e=plain_prefix_pattern                    { e }
  | t=var_name ps=prefix_pattern+             { Patt_Constr (t, ps) }

prefix_pattern: mark_location(plain_prefix_pattern) { $1 }
plain_prefix_pattern:
  | e=plain_simple_pattern            { e }
  | oploc=prefix e=prefix_pattern
    { let (op, _) = oploc in
      Patt_Constr (op, [e])
    }

simple_pattern: mark_location(plain_simple_pattern) { $1 }
plain_simple_pattern:
  | UNDERSCORE                     { Patt_Anonymous }
  | x=patt_var                     { Patt_Var x }
  | x=var_name                     { Patt_Name x }
  | LPAREN ps=separated_list(COMMA, pattern) RPAREN
    { match ps with
      | [{Location.thing=p;loc=_}] -> p
      | _ -> Patt_Tuple ps
    }
  | LBRACK ps=separated_list(COMMA, pattern) RBRACK { Patt_List ps }

tt_pattern: mark_location(plain_tt_pattern) { $1 }
plain_tt_pattern:
  | p=plain_equal_tt_pattern                     { p }
  | LAMBDA a=tt_abstraction COMMA p=tt_pattern   { Tt_Lambda (a, p) }
  | PROD a=tt_abstraction COMMA p=tt_pattern     { Tt_Prod (a, p) }
  | p1=equal_tt_pattern ARROW p2=tt_pattern      { Tt_Prod ([(NonPattVar (Name.anonymous ()), Some p1)], p2) }
  | p=app_tt_pattern AS x=patt_var               { Tt_As (p,x) }

equal_tt_pattern: mark_location(plain_equal_tt_pattern) { $1 }
plain_equal_tt_pattern:
  | p=plain_binop_tt_pattern                      { p }
  | p1=binop_tt_pattern EQEQ p2=binop_tt_pattern  { Tt_Eq (p1, p2) }

binop_tt_pattern: mark_location(plain_binop_tt_pattern) { $1 }
plain_binop_tt_pattern:
  | p=plain_app_tt_pattern                        { p }
  | e1=binop_tt_pattern oploc=infix e2=binop_tt_pattern
    { let (op, loc) = oploc in
      let op = Location.locate (Tt_Name op) loc in
      Tt_Spine (op, [e1; e2])
    }

app_tt_pattern: mark_location(plain_app_tt_pattern) { $1 }
plain_app_tt_pattern:
  | p=plain_prefix_tt_pattern                                { p }
  | p=prefix_tt_pattern ps=nonempty_list(prefix_tt_pattern)  { Tt_Spine (p, ps) }

prefix_tt_pattern: op=mark_location(plain_prefix_tt_pattern) { op }
plain_prefix_tt_pattern:
  | p=plain_simple_tt_pattern        { p }
  | REFL p=prefix_tt_pattern         { Tt_Refl p }
  | UATOM p=prefix_tt_pattern        { Tt_GenAtom p }
  | UCONSTANT p=prefix_tt_pattern    { Tt_GenConstant p }
  | oploc=prefix e=prefix_tt_pattern
    { let (op, loc) = oploc in
      let op = Location.locate (Tt_Name op) loc in
      Tt_Spine (op, [e])
    }

plain_simple_tt_pattern:
  | UNDERSCORE                                                           { Tt_Anonymous }
  | TYPE                                                                 { Tt_Type }
  | x=patt_var                                                           { Tt_Var x }
  | x=var_name                                                           { Tt_Name x }
  | LPAREN p=plain_tt_pattern RPAREN                                     { p }

(* The TT pattern for abstraction follows the lambda abstraction syntax *)
tt_name:
  | x=var_name      { NonPattVar x }
  | UNDERSCORE      { PattVar (Name.anonymous ()) }
  | x=PATTVAR       { PattVar x }

patt_var:
  | x=PATTVAR                    { x }

(* TODO It is likely that tt_typed_binder and typed_binder share enough structure that
   they could be unified and presented as two instances of the same thing. *)
tt_typed_binder:
  | LPAREN xs=tt_name+ COLON t=tt_pattern RPAREN         { List.map (fun x -> (x, t)) xs }

tt_maybe_typed_binder:
  | x=tt_name                                            { [(x, None)] }
  | LPAREN xs=tt_name+ COLON t=tt_pattern RPAREN         { List.map (fun x -> (x, Some t)) xs }

tt_abstraction:
  | lam=raw_nonempty_tt_abstraction { fst lam }

raw_nonempty_tt_abstraction:
  | x=tt_name lam=raw_tt_abstraction
    { let (l,t) = lam in ((x,t)::l,t) }
  | xs=tt_typed_binder ys=tt_maybe_typed_binder*
    { ((List.map (fun (x,t) -> (x,Some t)) xs) @ (List.concat ys), None) }

raw_tt_abstraction:
  | { ([],None) }
  | COLON t=tt_pattern { ([],Some t) }
  | x=tt_name lam=raw_tt_abstraction
    { let (l,t) = lam in ((x,t)::l,t) }
  | xs=tt_typed_binder ys=tt_maybe_typed_binder*
    { ((List.map (fun (x,t) -> (x,Some t)) xs) @ (List.concat ys), None) }

(***)


(* ML types *)

op_mlsig:
  | lst=separated_nonempty_list(ARROW, prod_mlty)
    { match List.rev lst with
      | t :: ts -> (List.rev ts, t)
      | [] -> assert false
     }

ml_schema: mark_location(plain_ml_schema) { $1 }
plain_ml_schema:
  | PROD params=var_name+ COMMA t=mlty    { ML_Forall (params, t) }
  | t=mlty                                { ML_Forall ([], t) }

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
  | plain_simple_mlty                          { $1 }
  | REF t=simple_mlty                          { ML_Ref t }
  | DYNAMIC t=simple_mlty                      { ML_Dynamic t }
  | c=var_name args=nonempty_list(simple_mlty) { ML_TyApply (c, args) }

simple_mlty: mark_location(plain_simple_mlty) { $1 }
plain_simple_mlty:
  | LPAREN t=plain_mlty RPAREN          { t }
  | c=var_name                          { ML_TyApply (c, []) }
  | JUDGMENT                            { ML_Judgment }
  | MLUNIT                              { ML_Prod [] }
  | MLSTRING                            { ML_String }
  | UNDERSCORE                          { ML_Anonymous }

mlty_defs:
  | lst=separated_nonempty_list(AND, mlty_def) { lst }

mlty_def:
  | a=var_name xs=list(name) EQ body=mlty_def_body { (a, (xs, body)) }

mlty_def_body:
  | t=mlty                                                       { ML_Alias t }
  | lst=separated_list(BAR, mlty_constructor) END                { ML_Sum lst }
  | BAR lst=separated_nonempty_list(BAR, mlty_constructor) END   { ML_Sum lst }

mlty_constructor:
  | c=var_name OF lst=separated_nonempty_list(AND, mlty)      { (c, lst) }
  | c=var_name                                                { (c, []) }

mark_location(X):
  x=X
  { Location.locate x (Location.make $startpos $endpos) }
%%
