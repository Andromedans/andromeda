%{
  open Input

  let tt_spine h lst =
    let loc = snd h in
    List.fold_left (fun h e -> Tt_App (h, e), loc) h lst

%}

(* Type *)
%token TYPE

(* Products *)
%token PROD LAMBDA

(* Records *)
%token <string> PROJECTION
%token AS

(* Infix operations *)
%token <string * Location.t> PREFIXOP INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4

(* Equality types *)
%token EQEQ
%token REFL

(* Names and numerals *)
%token UNDERSCORE
%token <string> NAME
%token <int> NUMERAL

(* Parentheses & punctuations *)
%token LPAREN RPAREN
%token LBRACE RBRACE
%token LBRACK RBRACK
%token COLON COLONCOLON COMMA
%token ARROW DARROW

(* Things specific to toplevel *)
%token CHECK FAIL
%token CONSTANT REDUCE

(* Let binding *)
%token LET EQ AND IN

(* Meta-level programming *)
%token OPERATION
%token DATA
%token <string> PATTVAR
%token MATCH
%token VDASH

%token HANDLE WITH HANDLER BAR VAL FINALLY END YIELD
%token SEMICOLON

%token CONGRUENCE
%token CONTEXT
%token TYPEOF

%token EXTERNAL

(* REFERENCES *)
%token BANG COLONEQ REF

(* Functions *)
%token REC FUNCTION

(* Assumptions *)
%token ASSUME

(* Substitution *)
%token WHERE

(* Toplevel directives *)
%token ENVIRONMENT HELP QUIT
%token <int> VERBOSITY
%token <string> QUOTED_STRING
%token INCLUDE INCLUDEONCE

%token EOF

(* Precedence and fixity of infix operators *)
%nonassoc COLONEQ
%left     INFIXOP0
%right    INFIXOP1
%right    COLONCOLON
%left     INFIXOP2
%left     INFIXOP3
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
  | LET x=name yts=typed_binder* u=return_type? EQ c=term
       { TopLet (x, List.concat yts, u, c) }
  | LET REC x=name a=function_abstraction EQ e=term
       { TopLet (x, [], None, (Rec (x, a, e),snd e)) }
  | HANDLE lst=top_handler_cases END                  { TopHandle lst }
  | CHECK c=term                                      { TopCheck c }
  | FAIL c=term                                       { TopFail c }
  | CONSTANT x=name yst=constarg* COLON u=term        { Axiom (x, List.concat yst, u)}
  | DATA x=name k=NUMERAL                             { Data (x, k) }
  | OPERATION op=name k=NUMERAL                       { Operation (op, k) }

return_type:
  | COLON t=ty_term { t }

(* Toplevel directive. *)
topdirective: mark_location(plain_topdirective)      { $1 }
plain_topdirective:
  | ENVIRONMENT                                      { Environment }
  | HELP                                             { Help }
  | QUIT                                             { Quit }
  | VERBOSITY                                        { Verbosity $1 }
  | INCLUDE fs=QUOTED_STRING+                        { Include (fs, false) }
  | INCLUDEONCE fs=QUOTED_STRING+                    { Include (fs, true) }

(* Main syntax tree *)

term: mark_location(plain_term) { $1 }
plain_term:
  | e=plain_ty_term                                            { e }
  | LET a=let_clauses IN c=term                                { Let (a, c) }
  | LET REC x=name a=function_abstraction EQ e=term IN c=term  { Let ([x,(Rec (x, a, e),snd e)], c) }
  | ASSUME x=var_name COLON t=ty_term IN c=term                { Assume ((x, t), c) }
  | c1=equal_term WHERE e=simple_term EQ c2=term               { Where (c1, e, c2) }
  | MATCH e=term WITH lst=match_cases END                      { Match (e, lst) }
  | HANDLE c=term WITH hcs=handler_cases END                   { Handle (c, hcs) }
  | WITH h=term HANDLE c=term                                  { With (h, c) }
  | HANDLER hcs=handler_cases END                              { Handler (hcs) }
  | e=app_term COLON t=ty_term                                 { Ascribe (e, t) }
  | e1=equal_term SEMICOLON e2=term                            { Sequence (e1, e2) }

ty_term: mark_location(plain_ty_term) { $1 }
plain_ty_term:
  | e=plain_equal_term                               { e }
  | PROD a=typed_binder+ COMMA e=term                { Prod (List.concat a, e) }
  | PROD a=typed_names COMMA e=term                  { Prod (a, e) }
  | LAMBDA a=binder+ COMMA e=term                    { Lambda (List.concat a, e) }
  | LAMBDA a=maybe_typed_names COMMA e=term          { Lambda (a, e) }
  | FUNCTION a=function_abstraction DARROW e=term    { Function (a, e) }
  | REC x=name a=function_abstraction DARROW e=term  { Rec (x, a, e) }
  | t1=equal_term ARROW t2=ty_term                   { Prod ([(Name.anonymous, t1)], t2) }

equal_term: mark_location(plain_equal_term) { $1 }
plain_equal_term:
  | e=plain_binop_term                               { e }
  | e1=binop_term EQEQ e2=binop_term                 { Eq (e1, e2) }

binop_term: mark_location(plain_binop_term) { $1 }
plain_binop_term:
  | e=plain_app_term                                { e }
  | e1=app_term COLONEQ e2=binop_term               { Update (e1, e2) }
  | e1=binop_term COLONCOLON e2=binop_term          { Cons (e1, e2) }
  | e2=binop_term op=INFIXOP0 e3=binop_term
    { let e1 = Var (Name.make ~fixity:Name.Infix0 (fst op)), snd op in Spine (e1, [e2; e3]) }
  | e2=binop_term op=INFIXOP1 e3=binop_term
    { let e1 = Var (Name.make ~fixity:Name.Infix1 (fst op)), snd op in Spine (e1, [e2; e3]) }
  | e2=binop_term op=INFIXOP2 e3=binop_term
    { let e1 = Var (Name.make ~fixity:Name.Infix2 (fst op)), snd op in Spine (e1, [e2; e3]) }
  | e2=binop_term op=INFIXOP3 e3=binop_term
    { let e1 = Var (Name.make ~fixity:Name.Infix3 (fst op)), snd op in Spine (e1, [e2; e3]) }
  | e2=binop_term op=INFIXOP4 e3=binop_term
    { let e1 = Var (Name.make ~fixity:Name.Infix4 (fst op)), snd op in Spine (e1, [e2; e3]) }

app_term: mark_location(plain_app_term) { $1 }
plain_app_term:
  | e=plain_prefix_term                             { e }
  | e=prefix_term es=nonempty_list(prefix_term)     { match fst e with
                                                      | Tag (t, []) -> Tag (t, es)
                                                      | _ -> Spine (e, es) }
  | CONGRUENCE t1=prefix_term t2=prefix_term        { Congruence (t1,t2) }

prefix_term: mark_location(plain_prefix_term) { $1 }
plain_prefix_term:
  | e=plain_simple_term                        { e }
  | REF e=prefix_term                          { Ref e }
  | BANG e=prefix_term                         { Lookup e }
  | op=PREFIXOP e2=prefix_term                 { let e1 = Var (Name.make ~fixity:Name.Prefix (fst op)), snd op in
                                                 Spine (e1, [e2]) }
  | REDUCE t=prefix_term                       { Reduce t }
  | YIELD e=prefix_term                        { Yield e }
  | TYPEOF t=prefix_term                       { Typeof t }
  | REFL e=prefix_term                         { Refl e }

simple_term: mark_location(plain_simple_term) { $1 }
plain_simple_term:
  | TYPE                                            { Type }
  | x=var_name                                      { Var x }
  | EXTERNAL s=QUOTED_STRING                        { External s }
  | s=QUOTED_STRING                                 { String s }
  | LBRACK lst=separated_list(COMMA, equal_term) RBRACK { List lst }
  | LPAREN e=plain_term RPAREN                      { e }
  | LBRACE lst=separated_list(COMMA, signature_clause) RBRACE
        { Signature lst }
  | LPAREN RPAREN                                   { Structure [] }
  | LBRACE lst=separated_nonempty_list(COMMA, structure_clause) RBRACE
        { Structure lst }
  | e1=simple_term p=PROJECTION                     { Projection(e1,Name.make p) }
  | CONTEXT                                         { Context }

var_name:
  | NAME { Name.make $1 }
  | LPAREN op=PREFIXOP RPAREN  { Name.make ~fixity:Name.Prefix (fst op) }
  | LPAREN op=INFIXOP0 RPAREN  { Name.make ~fixity:Name.Infix0 (fst op) }
  | LPAREN op=INFIXOP1 RPAREN  { Name.make ~fixity:Name.Infix1 (fst op) }
  | LPAREN op=INFIXOP2 RPAREN  { Name.make ~fixity:Name.Infix2 (fst op) }
  | LPAREN op=INFIXOP3 RPAREN  { Name.make ~fixity:Name.Infix3 (fst op) }
  | LPAREN op=INFIXOP4 RPAREN  { Name.make ~fixity:Name.Infix4 (fst op) }

name:
  | x=var_name { x }
  | UNDERSCORE { Name.anonymous }

let_clauses:
  | ls=separated_nonempty_list(AND, let_clause)     { ls }

let_clause:
  | x=name EQ c=term                           { (x,c) }

typed_binder:
  | LPAREN lst=separated_nonempty_list(COMMA, typed_names) RPAREN
       { List.concat lst }

typed_names:
  | xs=name+ COLON t=ty_term  { List.map (fun x -> (x, t)) xs }

signature_clause:
  | x=name COLON t=ty_term           { (x, None, t) }
  | x=name AS y=name COLON t=ty_term { (x, Some y, t) }

structure_clause :
  | x=name EQ c=term                           { (x, None, c) }
  | x=name AS y=name EQ c=term                 { (x, Some y, c) }

binder:
  | LPAREN lst=separated_nonempty_list(COMMA, maybe_typed_names) RPAREN
      { List.concat lst }

maybe_typed_names:
  | xs=name+ COLON t=ty_term  { List.map (fun x -> (x, Some t)) xs }
  | xs=name+                  { List.map (fun x -> (x, None)) xs }

constarg:
  | LPAREN lst=separated_nonempty_list(COMMA, constarg_entry) RPAREN  { List.concat lst }

constarg_entry:
  | xs=nonempty_list(name) COLON t=ty_term   { List.map (fun x -> (x, t)) xs }

(* function arguments *)
function_abstraction:
  | xs = nonempty_list(name)     { xs }

handler_cases:
  | BAR lst=separated_nonempty_list(BAR, handler_case)  { lst }
  | lst=separated_list(BAR, handler_case)               { lst }

handler_case:
  | VAL p=pattern DARROW t=term                                 { CaseVal (p, t) }
  | op=var_name ps=prefix_pattern* DARROW t=term                { CaseOp (op, (ps, t)) }
  | op=PREFIXOP p=prefix_pattern DARROW t=term
    { let op = Name.make ~fixity:Name.Prefix (fst op) in CaseOp (op, ([p], t)) }
  | p1=binop_pattern op=INFIXOP0 p2=binop_pattern DARROW t=term
    { let op = Name.make ~fixity:Name.Infix0 (fst op) in CaseOp (op, ([p1; p2], t)) }
  | p1=binop_pattern op=INFIXOP1 p2=binop_pattern DARROW t=term
    { let op = Name.make ~fixity:Name.Infix1 (fst op) in CaseOp (op, ([p1; p2], t)) }
  | p1=binop_pattern op=INFIXOP2 p2=binop_pattern DARROW t=term
    { let op = Name.make ~fixity:Name.Infix2 (fst op) in CaseOp (op, ([p1; p2], t)) }
  | p1=binop_pattern op=INFIXOP3 p2=binop_pattern DARROW t=term
    { let op = Name.make ~fixity:Name.Infix3 (fst op) in CaseOp (op, ([p1; p2], t)) }
  | p1=binop_pattern op=INFIXOP4 p2=binop_pattern DARROW t=term
    { let op = Name.make ~fixity:Name.Infix4 (fst op) in CaseOp (op, ([p1; p2], t)) }
  | FINALLY p=pattern DARROW t=term                             { CaseFinally (p, t) }

top_handler_cases:
  | BAR lst=separated_nonempty_list(BAR, top_handler_case)  { lst }
  | lst=separated_list(BAR, top_handler_case)               { lst }

(* XXX allow patterns here *)
top_handler_case:
  | op=var_name xs=name* DARROW t=term                    { (op, xs, t) }
  | op=PREFIXOP x=name DARROW t=term
    { let op = Name.make ~fixity:Name.Prefix (fst op) in (op, [x], t) }
  | x1=name op=INFIXOP0 x2=name DARROW t=term
    { let op = Name.make ~fixity:Name.Infix0 (fst op) in (op, [x1;x2], t) }
  | x1=name op=INFIXOP1 x2=name DARROW t=term
    { let op = Name.make ~fixity:Name.Infix1 (fst op) in (op, [x1;x2], t) }
  | x1=name op=INFIXOP2 x2=name DARROW t=term
    { let op = Name.make ~fixity:Name.Infix2 (fst op) in (op, [x1;x2], t) }
  | x1=name op=INFIXOP3 x2=name DARROW t=term
    { let op = Name.make ~fixity:Name.Infix3 (fst op) in (op, [x1;x2], t) }
  | x1=name op=INFIXOP4 x2=name DARROW t=term
    { let op = Name.make ~fixity:Name.Infix4 (fst op) in (op, [x1;x2], t) }

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
  | VDASH e1=tt_pattern COLON e2=tt_pattern { Patt_Jdg (e1, e2) }
  | VDASH e1=tt_pattern                     { Patt_Jdg (e1, (Tt_Anonymous, snd e1)) }

binop_pattern: mark_location(plain_binop_pattern) { $1 }
plain_binop_pattern:
  | e=plain_app_pattern                                { e }
  | e1=binop_pattern op=INFIXOP0 e2=binop_pattern
    { let op = Name.make ~fixity:Name.Infix0 (fst op) in Patt_Tag (op, [e1; e2]) }
  | e1=binop_pattern op=INFIXOP1 e2=binop_pattern
    { let op = Name.make ~fixity:Name.Infix1 (fst op) in Patt_Tag (op, [e1; e2]) }
  | e1=binop_pattern COLONCOLON  e2=binop_pattern
    { Patt_Cons (e1, e2) }
  | e1=binop_pattern op=INFIXOP2 e2=binop_pattern
    { let op = Name.make ~fixity:Name.Infix2 (fst op) in Patt_Tag (op, [e1; e2]) }
  | e1=binop_pattern op=INFIXOP3 e2=binop_pattern
    { let op = Name.make ~fixity:Name.Infix3 (fst op) in Patt_Tag (op, [e1; e2]) }
  | e1=binop_pattern op=INFIXOP4 e2=binop_pattern
    { let op = Name.make ~fixity:Name.Infix4 (fst op) in Patt_Tag (op, [e1; e2]) }

(* app_pattern: mark_location(plain_app_pattern) { $1 } *)
plain_app_pattern:
  | e=plain_prefix_pattern                    { e }
  | t=var_name ps=prefix_pattern+             { Patt_Tag (t, ps) }

prefix_pattern: mark_location(plain_prefix_pattern) { $1 }
plain_prefix_pattern:
  | e=plain_simple_pattern           { e }
  | op=PREFIXOP e=prefix_pattern     { let op = Name.make ~fixity:Name.Prefix (fst op) in Patt_Tag (op, [e]) }

simple_pattern: mark_location(plain_simple_pattern) { $1 }
plain_simple_pattern:
  | UNDERSCORE                     { Patt_Anonymous }
  | x=patt_var                     { Patt_Var x }
  | x=var_name                     { Patt_Name x }
  | LPAREN p=plain_pattern RPAREN  { p }
  | LBRACK ps=separated_list(COMMA, pattern) RBRACK { Patt_List ps }

tt_pattern: mark_location(plain_tt_pattern) { $1 }
plain_tt_pattern:
  | p=plain_equal_tt_pattern                  { p }
  | LAMBDA bs=tt_binder+ COMMA p=tt_pattern   { fst (List.fold_right
                                                       (fun ((x, b, pt), loc) p -> Tt_Lambda (b, x, pt, p), loc)
                                                       (List.concat bs) p)
                                               }
  | PROD bs=tt_binder+ COMMA p=tt_pattern     { fst (List.fold_right
                                                       (fun ((x, b, pt), loc) p -> Tt_Prod (b, x, pt, p), loc)
                                                       (List.concat bs) p)
                                              } 
  | p1=equal_tt_pattern ARROW p2=tt_pattern   { Tt_Prod (false, Name.anonymous, Some p1, p2) }

equal_tt_pattern: mark_location(plain_equal_tt_pattern) { $1 }
plain_equal_tt_pattern:
  | p=plain_binop_tt_pattern                      { p }
  | p1=binop_tt_pattern EQEQ p2=binop_tt_pattern  { Tt_Eq (p1, p2) }

binop_tt_pattern: mark_location(plain_binop_tt_pattern) { $1 }
plain_binop_tt_pattern:
  | p=plain_app_tt_pattern                        { p }
  | e1=binop_tt_pattern op=INFIXOP0 e2=binop_tt_pattern
    { let op = Tt_Name (Name.make ~fixity:Name.Infix0 (fst op)), snd op in fst (tt_spine op [e1; e2]) }
  | e1=binop_tt_pattern op=INFIXOP1 e2=binop_tt_pattern
    { let op = Tt_Name (Name.make ~fixity:Name.Infix1 (fst op)), snd op in fst (tt_spine op [e1; e2]) }
  | e1=binop_tt_pattern op=INFIXOP2 e2=binop_tt_pattern
    { let op = Tt_Name (Name.make ~fixity:Name.Infix2 (fst op)), snd op in fst (tt_spine op [e1; e2]) }
  | e1=binop_tt_pattern op=INFIXOP3 e2=binop_tt_pattern
    { let op = Tt_Name (Name.make ~fixity:Name.Infix3 (fst op)), snd op in fst (tt_spine op [e1; e2]) }
  | e1=binop_tt_pattern op=INFIXOP4 e2=binop_tt_pattern
    { let op = Tt_Name (Name.make ~fixity:Name.Infix4 (fst op)), snd op in fst (tt_spine op [e1; e2]) }

app_tt_pattern: mark_location(plain_app_tt_pattern) { $1 }
plain_app_tt_pattern:
  | p=plain_prefix_tt_pattern                 { p }
  | p=app_tt_pattern AS x=patt_var            { Tt_As (p,x) }
  | p1=app_tt_pattern p2=prefix_tt_pattern    { Tt_App (p1, p2) }

prefix_tt_pattern: mark_location(plain_prefix_tt_pattern) { $1 }
plain_prefix_tt_pattern:
  | p=plain_simple_tt_pattern                 { p }
  | REFL p=prefix_tt_pattern                  { Tt_Refl p }
  | op=PREFIXOP e=prefix_tt_pattern
    { let op = Tt_Name (Name.make ~fixity:Name.Infix4 (fst op)), snd op in Tt_App (op, e) }

simple_tt_pattern: mark_location(plain_simple_tt_pattern) { $1 }
plain_simple_tt_pattern:
  | UNDERSCORE                                                           { Tt_Anonymous }
  | TYPE                                                                 { Tt_Type }
  | x=patt_var                                                           { Tt_Var x }
  | x=var_name                                                           { Tt_Name x }
  | LPAREN p=plain_tt_pattern RPAREN                                     { p }
  | LBRACE ps=separated_list(COMMA, tt_signature_clause) RBRACE          { Tt_Signature ps }
  | LPAREN RPAREN                                                        { Tt_Structure [] }
  | LBRACE ps=separated_nonempty_list(COMMA, tt_structure_clause) RBRACE { Tt_Structure ps }
  | p=simple_tt_pattern lbl=PROJECTION                                   { Tt_Projection (p, Name.make lbl) }

tt_signature_clause:
  | x=tt_name COLON p=tt_pattern           { let (x,b) = x in (x, b, None, p) }
  | x=name AS y=tt_name COLON p=tt_pattern { let (y,b) = y in (x, b, Some y, p) }

tt_structure_clause:
  | x=tt_name EQ c=tt_pattern           { let (x,b) = x in (x, b, None, c) }
  | x=name AS y=tt_name EQ c=tt_pattern { let (y,b) = y in (x, b, Some y, c) }

tt_binder:
  | LPAREN lst=separated_nonempty_list(COMMA, maybe_typed_tt_names) RPAREN
      { List.concat (List.map (fun (xs, loc) -> List.map (fun x -> x, loc) xs) lst) }

maybe_typed_tt_names: mark_location(plain_maybe_typed_tt_names) { $1 }
plain_maybe_typed_tt_names:
  | xs=tt_name+ COLON p=tt_pattern  { List.map (fun (x,b) -> (x, b, Some p)) xs }
  | xs=tt_name+                     { List.map (fun (x,b) -> (x, b, None)) xs }

tt_name:
  | x=name                       { x, false }
  | x=patt_var                   { x, true  }

patt_var:
  | x=PATTVAR                    { Name.make x }

mark_location(X):
  x=X
  { x, Location.make $startpos $endpos }
%%
