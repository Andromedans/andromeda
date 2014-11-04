%{
  open Input

  (* Build nested lambdas *)
  let rec make_lambda e = function
    | [] -> e
    | ((xs, t), loc) :: lst ->
      let e = make_lambda e lst in
        List.fold_right (fun x e -> (Lambda (x, t, e), loc)) xs e

  (* Build nested name pi's *)
  let rec make_prod e = function
    | [] -> e
    | ((xs, t), loc) :: lst ->
      let e = make_prod e lst in
        List.fold_right (fun x e -> (Prod (x, t, e), loc)) xs e

%}

%token FORALL FUN
%token TYPE
%token UNDERSCORE
%token <string> NAME
%token LPAREN RPAREN
%token COLON ASCRIBE COMMA DOT
%token ARROW DARROW
%token EQEQ
%token REFL
%token TOPLET TOPCHECK
%token LET COLONEQ IN
%token PARAMETER
%token CONTEXT HELP QUIT
%token EOF

%start <Input.toplevel list> file
%start <Input.toplevel> commandline

%%

(* Toplevel syntax *)

file:
  | f=filecontents EOF            { f }

filecontents:
  |                                 { [] }
  | d=topcomp ds=filecontents        { d :: ds }
  | d=topdirective ds=filecontents  { d :: ds }

commandline:
  | topcomp EOF       { $1 }
  | topdirective EOF { $1 }

(* Things that can be defined on toplevel. *)
topcomp: mark_position(plain_topcomp) { $1 }
plain_topcomp:
  | TOPLET x=NAME COLONEQ c=comp DOT                  { TopLet (x, c) }
  | TOPCHECK c=comp DOT                               { TopCheck c }
  | PARAMETER xs=nonempty_list(NAME) COLON t=ty DOT   { Parameter (xs, t) }
    
(* Toplevel directive. *)
topdirective: mark_position(plain_topdirective) { $1 }
plain_topdirective:
  | CONTEXT    { Context }
  | HELP       { Help }
  | QUIT       { Quit }

(* Main syntax tree *)

comp: mark_position(plain_comp) { $1 }
plain_comp:
  | LET x=NAME COLONEQ c1=simple_comp IN c2=comp    { Let (x, c1, c2) }
  | c=plain_simple_comp                             { c }

simple_comp: mark_position(plain_simple_comp) { $1 }
plain_simple_comp:
  | e=term { Term e }                            

term: mark_position(plain_term) { $1 }
plain_term:
  | e=plain_equal_term                              { e }
  | FORALL a=abstraction(term) COMMA e=term         { fst (make_prod e a) }
  | FUN a=abstraction(ty) DARROW e=term             { fst (make_lambda e a) }
  | e=equal_term ASCRIBE t=ty                       { Ascribe (e, t) }
  | t1=equal_term ARROW t2=ty                       { Prod (anonymous, t1, t2) }

equal_term: mark_position(plain_equal_term) { $1 }
plain_equal_term:
    | e=plain_app_term               { e }
    | e1=app_term EQEQ e2=app_term   { Eq (e1, e2) }

app_term: mark_position(plain_app_term) { $1 }
plain_app_term:
  | e=plain_simple_term                          { e }
  | e1=app_term e2=simple_term                   { App (e1, e2) }
  | REFL e=simple_term                           { Refl e }

param:
  | NAME { $1 }
  | UNDERSCORE { anonymous }

simple_term: mark_position(plain_simple_term) { $1 }
plain_simple_term:
  | TYPE                         { Type }
  | x=NAME                       { Var x }
  | LPAREN e=plain_term RPAREN   { e }

ty:
  | t=term { t }

(* returns a list of things individually annotated by positions.
  Since the list is not further annotated, consistency suggests
  this should be called plain_abstraction, but as we know,
  consistency is the hemoglobin of mindless lights. *)
abstraction(X):
  | bind(X)                            { [$1] }
  | nonempty_list(paren_bind(X))       { $1 }

bind(X): mark_position(plain_bind(X)) { $1 }
plain_bind(X):
  | xs=nonempty_list(param) COLON t=X { (xs, t) }

paren_bind(X):
  | LPAREN b=bind(X) RPAREN           { b }

mark_position(X):
  x=X
  { x, Position.make $startpos $endpos }

%%
