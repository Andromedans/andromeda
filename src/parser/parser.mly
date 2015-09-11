%{
  open Input
%}

%token FORALL LAMBDA
%token TYPE
%token UNDERSCORE
%token <string> NAME
%token LPAREN RPAREN LBRACK RBRACK LRBRACK LLBRACK RRBRACK
%token DCOLON COLON SEMICOLON COMMA DOT
%token ARROW
%token EQEQ
%token REFL
%token TOPLET TOPCHECK TOPBETA TOPETA TOPHINT TOPINHABIT
%token TOPUNHINT
%token LET COLONEQ AND IN
%token BETA ETA HINT INHABIT
%token UNHINT
%token HANDLE HANDLER WITH BAR VAL FINALLY END
%token WHNF TYPEOF
%token FUNCTION APPLY
%token AXIOM REDUCE
%token <string> OPERATION
%token CONTEXT HELP QUIT
%token <int> VERBOSITY
%token <string> QUOTED_STRING
%token INCLUDE
%token EOF

%start <Input.toplevel list> file
%start <Input.toplevel> commandline
%start <Input.toplevel> command

%%

(* Toplevel syntax *)

file:
  | f=filecontents EOF            { f }

filecontents:
  |                                 { [] }
  | d=topcomp DOT ds=filecontents       { d :: ds }
  | d=topdirective DOT ds=filecontents  { d :: ds }

command:
  | d=topcomp DOT       { d }
  | d=topdirective DOT  { d }

commandline:
  | topcomp DOT EOF       { $1 }
  | topdirective DOT EOF { $1 }

(* Things that can be defined on toplevel. *)
topcomp: mark_location(plain_topcomp) { $1 }
plain_topcomp:
  | TOPLET x=name yts=typed_binder* u=return_type? COLONEQ c=term { TopLet (x, List.concat yts, u, c) }
  | TOPCHECK c=term                                  { TopCheck c }
  | TOPBETA ths=tags_hints                           { TopBeta ths }
  | TOPETA ths=tags_hints                            { TopEta ths }
  | TOPHINT ths=tags_hints                           { TopHint ths }
  | TOPINHABIT ths=tags_hints                        { TopInhabit ths }
  | TOPUNHINT ts=tags_unhints                        { TopUnhint ts }
  | AXIOM x=name yst=primarg* COLON u=term           { Axiom (x, List.concat yst, u)}

return_type:
  | COLON t=ty_term { t }

(* Toplevel directive. *)
topdirective: mark_location(plain_topdirective) { $1 }
plain_topdirective:
  | CONTEXT    { Context }
  | HELP       { Help }
  | QUIT       { Quit }
  | VERBOSITY                                            { Verbosity $1 }
  | INCLUDE fs=quoted_string+                            { Include fs }

quoted_string:
  | QUOTED_STRING { let s = $1 in
               let l = String.length s in
               String.sub s 1 (l - 2) }

(* Main syntax tree *)

term: mark_location(plain_term) { $1 }
plain_term:
  | e=plain_ty_term                                 { e }
  | LET a=let_clauses IN c=term                     { Let (a, c) }
  | BETA tshs=tags_opt_hints IN c=term              { Beta (tshs, c) }
  | ETA tshs=tags_opt_hints IN c=term               { Eta (tshs, c) }
  | HINT tshs=tags_opt_hints IN c=term              { Hint (tshs, c) }
  | INHABIT tshs=tags_opt_hints IN c=term           { Inhabit (tshs, c) }
  | UNHINT ts=tags_unhints IN c=term                { Unhint (ts, c) }
  | HANDLE c=term WITH hcs=handler_case* END        { Handle (c, hcs) }
  | WITH h=term HANDLE c=term                       { With (h, c) }
  | HANDLER hcs=handler_case* END                   { Handler (hcs) }
  | e=app_term DCOLON t=ty_term                     { Ascribe (e, t) }

ty_term: mark_location(plain_ty_term) { $1 }
plain_ty_term:
  | e=plain_equal_term                              { e }
  | FORALL a=typed_binder+ e=term                   { Prod (List.concat a, e) }
  | LAMBDA a=binder+ e=term                         { Lambda (List.concat a, e) }
  | FUNCTION a=function_abstraction ARROW e=term    { Function (a, e) }
  | t1=equal_term ARROW t2=ty_term                  { Prod ([(Name.anonymous, t1)], t2) }

equal_term: mark_location(plain_equal_term) { $1 }
plain_equal_term:
  | e=plain_app_term                                { e }
  | e1=app_term EQEQ e2=app_term                    { Eq (e1, e2) }

app_term: mark_location(plain_app_term) { $1 }
plain_app_term:
  | e=plain_simple_term                             { e }
  | e=simple_term es=nonempty_list(simple_term)     { Spine (e, es) }
  | e1=simple_term APPLY e2=app_term                { Apply (e1, e2) }
  | WHNF t=simple_term                              { Whnf t }
  | TYPEOF t=simple_term                            { Typeof t }
  | REFL e=simple_term                              { Refl e }
  | op=OPERATION e=simple_term                      { Operation (op, e) }

simple_term: mark_location(plain_simple_term) { $1 }
plain_simple_term:
  | TYPE                                            { Type }
  | LRBRACK                                         { Inhab }
  | x=var_name                                      { Var x }
  | LPAREN e=plain_term RPAREN                      { e }
  | LLBRACK e=term RRBRACK                          { Bracket e }

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

binder:
  | LBRACK lst=separated_nonempty_list(COMMA, maybe_typed_names) RBRACK
      { List.concat lst }

maybe_typed_names:
  | xs=name+ COLON t=ty_term  { List.map (fun x -> (x, Some t)) xs }
  | xs=name+                  { List.map (fun x -> (x, None)) xs }

primarg:
  | LBRACK lst=separated_nonempty_list(COMMA, primarg_entry) RBRACK  { List.concat lst }

primarg_entry:
  | b=reduce xs=nonempty_list(name) COLON t=ty_term   { List.map (fun x -> (x, b, t)) xs }

reduce:
  |        { false }
  | REDUCE { true }

(* function arguments *)
function_abstraction:
  | xs = nonempty_list(name)     { xs }

tags_hints:
  | tshs=separated_nonempty_list(SEMICOLON, tags_hint)     { List.flatten tshs }

(* local hints can be anonymous *)
tags_opt_hints:
  | tshs=separated_nonempty_list(SEMICOLON, tags_opt_hint) { List.flatten tshs }

tags_opt_hint:
  | t=tags_hint { t }
  | LPAREN t=term RPAREN   { [[], t] }

tags_hint:
  | t=var_hint { [t] }
  | xs=tag_var+ COLON ts=separated_nonempty_list(COMMA, term)
      { List.map (fun t ->
        let xs = match t with Var (Name.String x), _ -> x :: xs | _ -> xs
        in xs, t) ts }

var_hint:
  | x=mark_location(tag_var) { let (x, loc) = x in [x], (Var (Name.make x), loc) }

tag_var:
  | NAME { $1 }

tags_unhints:
  | ts=separated_nonempty_list(SEMICOLON, tags_unhint) { ts }

tags_unhint:
  | ts=tag_var { ts }

handler_case:
  | BAR VAL x=name ARROW t=term                 { CaseVal (x, t) }
  | BAR op=OPERATION x=name k=name ARROW t=term { CaseOp (op, x, k, t) }
  | BAR FINALLY x=name ARROW t=term             { CaseFinally (x, t) }

mark_location(X):
  x=X
  { x, Location.make $startpos $endpos }
%%
