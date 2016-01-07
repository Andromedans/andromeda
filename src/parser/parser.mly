%{
  open Input
%}

(* Type *)
%token TYPE

(* Products *)
%token PROD LAMBDA

(* Records *)
%token <string> PROJECTION
%token AS

(* Equality types *)
%token EQEQ
%token REFL

(* Patterns and names *)
%token UNDERSCORE
%token <string> NAME

(* Parentheses & punctuations *)
%token LPAREN RPAREN
%token LBRACK RBRACK
%token LBRACE RBRACE
%token DCOLON COLON COMMA
%token ARROW DARROW

(* Things specific to toplevel *)
%token CHECK
%token CONSTANT REDUCE

(* Let binding *)
%token LET COLONEQ AND IN

(* Meta-level programming *)
%token <string> TAG
%token <string> PATTVAR
%token MATCH
%token VDASH

%token <string> OPERATION
%token HANDLE WITH HANDLER BAR VAL FINALLY END YIELD

%token CONGRUENCE
%token CONTEXT
%token TYPEOF

%token EXTERNAL

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
%token INCLUDE

%token EOF

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
  | LET x=name yts=typed_binder* u=return_type? COLONEQ c=term 
       { TopLet (x, List.concat yts, u, c) }
  | LET REC x=name a=function_abstraction COLONEQ e=term
       { TopLet (x, [], None, (Rec (x, a, e),snd e)) }
  | HANDLE lst=top_handler_cases END                  { TopHandle lst }
  | CHECK c=term                                      { TopCheck c }
  | CONSTANT x=name yst=primarg* COLON u=term         { Axiom (x, List.concat yst, u)}

return_type:
  | COLON t=ty_term { t }

(* Toplevel directive. *)
topdirective: mark_location(plain_topdirective)      { $1 }
plain_topdirective:
  | ENVIRONMENT                                      { Environment }
  | HELP                                             { Help }
  | QUIT                                             { Quit }
  | VERBOSITY                                        { Verbosity $1 }
  | INCLUDE fs=QUOTED_STRING+                        { Include fs }

(* Main syntax tree *)

term: mark_location(plain_term) { $1 }
plain_term:
  | e=plain_ty_term                                                 { e }
  | LET a=let_clauses IN c=term                                     { Let (a, c) }
  | LET REC x=name a=function_abstraction COLONEQ e=term IN c=term  { Let ([x,(Rec (x, a, e),snd e)], c) }
  | ASSUME x=var_name COLON t=ty_term IN c=term                     { Assume ((x, t), c) }
  | c1=equal_term WHERE e=simple_term COLONEQ c2=term               { Where (c1, e, c2) }
  | MATCH e=term WITH lst=match_cases END                           { Match (e, lst) }
  | HANDLE c=term WITH hcs=handler_cases END                        { Handle (c, hcs) }
  | WITH h=term HANDLE c=term                                       { With (h, c) }
  | HANDLER hcs=handler_cases END                                   { Handler (hcs) }
  | e=app_term DCOLON t=ty_term                                     { Ascribe (e, t) }

ty_term: mark_location(plain_ty_term) { $1 }
plain_ty_term:
  | e=plain_equal_term                               { e }
  | PROD a=typed_binder+ e=term                      { Prod (List.concat a, e) }
  | LAMBDA a=binder+ e=term                          { Lambda (List.concat a, e) }
  | FUNCTION a=function_abstraction DARROW e=term    { Function (a, e) }
  | REC x=name a=function_abstraction DARROW e=term  { Rec (x, a, e) }
  | t1=equal_term ARROW t2=ty_term                   { Prod ([(Name.anonymous, t1)], t2) }

equal_term: mark_location(plain_equal_term) { $1 }
plain_equal_term:
  | e=plain_app_term                                { e }
  | e1=app_term EQEQ e2=app_term                    { Eq (e1, e2) }

app_term: mark_location(plain_app_term) { $1 }
plain_app_term:
  | e=plain_simple_term                             { e }
  | e=simple_term es=nonempty_list(simple_term)     { match fst e with
                                                      | Tag (t, []) -> Tag (t, es)
                                                      | _ -> Spine (e, es) }
  | CONGRUENCE t1=simple_term t2=simple_term        { Congruence (t1,t2) }
  | REDUCE t=simple_term                            { Reduce t }
  | TYPEOF t=simple_term                            { Typeof t }
  | REFL e=simple_term                              { Refl e }
  | op=OPERATION e=simple_term                      { Operation (op, e) }

simple_term: mark_location(plain_simple_term) { $1 }
plain_simple_term:
  | TYPE                                            { Type }
  | x=var_name                                      { Var x }
  | t=TAG                                           { Tag (Name.make t, []) }
  | EXTERNAL s=QUOTED_STRING                        { External s }
  | LPAREN e=plain_term RPAREN                      { e }
  | LBRACE lst=separated_list(COMMA, signature_clause) RBRACE
        { Signature lst }
  | LPAREN RPAREN                                   { Structure [] }
  | LBRACE lst=separated_nonempty_list(COMMA, structure_clause) RBRACE
        { Structure lst }
  | e1=simple_term p=PROJECTION                     { Projection(e1,Name.make p) }
  | CONTEXT                                         { Context }
  | YIELD                                           { Yield }

var_name:
  | NAME { Name.make $1 }

name:
  | x=var_name { x }
  | UNDERSCORE { Name.anonymous }

let_clauses:
  | ls=separated_nonempty_list(AND, let_clause)     { ls }

let_clause:
  | x=name COLONEQ c=term                           { (x,c) }

typed_binder:
  | LBRACK lst=separated_nonempty_list(COMMA, typed_names) RBRACK
       { List.concat lst }

typed_names:
  | xs=name+ COLON t=ty_term  { List.map (fun x -> (x, t)) xs }

signature_clause:
  | x=name COLON t=ty_term           { (x, None, t) }
  | x=name AS y=name COLON t=ty_term { (x, Some y, t) }

structure_clause :
  | x=name COLONEQ c=term                           { (x, None, c) }
  | x=name AS y=name COLONEQ c=term                 { (x, Some y, c) }

binder:
  | LBRACK lst=separated_nonempty_list(COMMA, maybe_typed_names) RBRACK
      { List.concat lst }

maybe_typed_names:
  | xs=name+ COLON t=ty_term  { List.map (fun x -> (x, Some t)) xs }
  | xs=name+                  { List.map (fun x -> (x, None)) xs }

primarg:
  | LBRACK lst=separated_nonempty_list(COMMA, primarg_entry) RBRACK  { List.concat lst }

primarg_entry:
  | b=reduce xs=nonempty_list(name) COLON t=ty_term   { List.map (fun x -> (b, (x, t))) xs }

reduce:
  |        { false }
  | REDUCE { true }

(* function arguments *)
function_abstraction:
  | xs = nonempty_list(name)     { xs }

handler_cases:
  | BAR lst=separated_nonempty_list(BAR, handler_case)  { lst }
  | lst=separated_list(BAR, handler_case)               { lst }

handler_case:
  | VAL p=pattern DARROW t=term                 { CaseVal (p, t) }
  | op=OPERATION p=pattern DARROW t=term        { CaseOp (op, p, t) }
  | FINALLY p=pattern DARROW t=term             { CaseFinally (p, t) }

top_handler_cases:
  | BAR lst=separated_nonempty_list(BAR, top_handler_case)  { lst }
  | lst=separated_list(BAR, top_handler_case)               { lst }

(* XXX allow patterns here *)
top_handler_case:
  | op=OPERATION x=name DARROW t=term        { (op, x, t) }

match_cases:
  | BAR lst=separated_nonempty_list(BAR, match_case)  { lst }
  | lst=separated_list(BAR, match_case)               { lst }

match_case:
  | p=pattern DARROW c=term  { (p, c) }


(** Pattern matching *)

pattern: mark_location(plain_pattern) { $1 }
plain_pattern:
  | p=plain_simple_pattern                  { p }
  | p=simple_pattern AS x=patt_var          { Patt_As (p,x) }
  | t=TAG ps=simple_pattern+                { Patt_Tag (Name.make t, ps) }
  | VDASH e1=tt_pattern COLON e2=tt_pattern { Patt_Jdg (e1, e2) }
  | VDASH e1=tt_pattern                     { Patt_Jdg (e1, (Tt_Anonymous, snd e1)) }


simple_pattern: mark_location(plain_simple_pattern) { $1 }
plain_simple_pattern:
  | UNDERSCORE                     { Patt_Anonymous }
  | x=patt_var                     { Patt_Var x }
  | x=var_name                     { Patt_Name x } 
  | t=TAG                          { Patt_Tag (Name.make t, []) }
  | LPAREN p=plain_pattern RPAREN  { p }

tt_pattern: mark_location(plain_tt_pattern) { $1 }
plain_tt_pattern:
  | p=plain_equal_tt_pattern                  { p }
  | LAMBDA bs=tt_binder+ p=tt_pattern         { fst (List.fold_right
                                                       (fun ((x, b, pt), loc) p -> Tt_Lambda (b, x, pt, p), loc)
                                                       (List.concat bs) p)
                                               }
  | PROD bs=tt_binder+ p=tt_pattern           { fst (List.fold_right
                                                       (fun ((x, b, pt), loc) p -> Tt_Prod (b, x, pt, p), loc)
                                                       (List.concat bs) p)
                                              } 
  | p1=equal_tt_pattern ARROW p2=tt_pattern   { Tt_Prod (false, Name.anonymous, Some p1, p2) }

equal_tt_pattern: mark_location(plain_equal_tt_pattern) { $1 }
plain_equal_tt_pattern:
  | p=plain_app_tt_pattern                    { p }
  | p1=app_tt_pattern EQEQ p2=app_tt_pattern  { Tt_Eq (p1, p2) }

app_tt_pattern: mark_location(plain_app_tt_pattern) { $1 }
plain_app_tt_pattern:
  | p=plain_simple_tt_pattern                 { p }
  | p=app_tt_pattern AS x=patt_var            { Tt_As (p,x) }
  | p1=app_tt_pattern p2=simple_tt_pattern    { Tt_App (p1, p2) }
  | REFL p=simple_tt_pattern                  { Tt_Refl p }

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
  | x=tt_name COLONEQ c=tt_pattern           { let (x,b) = x in (x, b, None, c) }
  | x=name AS y=tt_name COLONEQ c=tt_pattern { let (y,b) = y in (x, b, Some y, c) }

tt_binder:
  | LBRACK lst=separated_nonempty_list(COMMA, maybe_typed_tt_names) RBRACK
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
