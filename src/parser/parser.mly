%{
  open Input
%}

%token FORALL FUN
%token TYPE
%token UNDERSCORE
%token <string> NAME
%token LPAREN RPAREN LBRACK RBRACK
%token COLON COMMA DOT
%token ARROW DARROW
%token EQEQ
%token REFL
%token TOPLET TOPCHECK TOPBETA TOPETA TOPHINT TOPINHABIT
%token LET COLONEQ AND IN
%token BETA ETA HINT INHABIT
%token PRIMITIVE REDUCE
%token CONTEXT HELP QUIT
%token <int> VERBOSITY
%token <string> FILENAME
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
  | TOPLET x=name COLONEQ c=term DOT                     { TopLet (x, c) }
  | TOPCHECK c=term DOT                                  { TopCheck c }
  | TOPBETA c=term DOT                                   { TopBeta c }
  | TOPETA c=term DOT                                    { TopEta c }
  | TOPHINT c=term DOT                                   { TopHint c }
  | TOPINHABIT c=term DOT                                { TopInhabit c }
  | PRIMITIVE x=name yst=list(primarg) COLON u=term DOT { Primitive (x, List.concat yst, u)}

(* Toplevel directive. *)
topdirective: mark_location(plain_topdirective) { $1 }
plain_topdirective:
  | CONTEXT    { Context }
  | HELP       { Help }
  | QUIT       { Quit }
  | VERBOSITY                                            { Verbosity $1 }
  | INCLUDE fs=filename+                                 { Include fs }

filename:
  | FILENAME { let s = $1 in
               let l = String.length s in
               String.sub s 1 (l - 2) }

(* Main syntax tree *)

term: mark_location(plain_term) { $1 }
plain_term:
  | e=plain_ty_term                                 { e }
  | LET a=let_clauses IN c=term                     { Let (a, c) }
  | BETA e=term IN c=term                           { Beta (e, c) }
  | ETA e=term IN c=term                            { Eta (e, c) }
  | HINT e=term IN c=term                           { Hint (e, c) }
  | INHABIT e=term IN c=term                        { Inhabit (e, c) }
  | e=app_term COLON t=ty_term                      { Ascribe (e, t) }

ty_term: mark_location(plain_ty_term) { $1 }
plain_ty_term:
  | e=plain_equal_term                              { e }
  | FORALL a=abstraction(ty_term) COMMA e=term      { Prod (a, e) }
  | FUN a=fun_abstraction e=term                    { Lambda (a, e) }
  | t1=equal_term ARROW t2=ty_term                  { Prod ([(Name.anonymous, t1)], t2) }

equal_term: mark_location(plain_equal_term) { $1 }
plain_equal_term:
  | e=plain_app_term                                { e }
  | e1=app_term EQEQ e2=app_term                    { Eq (e1, e2) }

app_term: mark_location(plain_app_term) { $1 }
plain_app_term:
  | e=plain_simple_term                             { e }
  | e=simple_term es=nonempty_list(simple_term)     { Spine (e, es) }
  | REFL e=simple_term                              { Refl e }

simple_term: mark_location(plain_simple_term) { $1 }
plain_simple_term:
  | TYPE                                            { Type }
  | LBRACK RBRACK                                   { Inhab }
  | x=var_name                                      { Var x }
  | LPAREN e=plain_term RPAREN                      { e }
  | LBRACK e=term RBRACK                            { Bracket e }

var_name:
  | NAME { Name.make $1 }

name:
  | x=var_name { x }
  | UNDERSCORE { Name.anonymous }

let_clauses:
  | ls=separated_nonempty_list(AND, let_clause)     { ls }

let_clause:
  | x=name COLONEQ c=term                           { (x,c) }

(* returns a list of things individually annotated by locations.
  Since the list is not further annotated, consistency suggests
  this should be called plain_abstraction, but as we know,
  consistency is the hemoglobin of mindless lights. *)
abstraction(X):
  | xst=bind(X)                        { xst }
  | xsts=nonempty_list(paren_bind(X))  { List.concat xsts }

bind(X):
  | xs=nonempty_list(name) COLON t=X   { List.map (fun x -> (x, t)) xs }

bind1(X):
  | x=name COLON t=X   { (x, t) }

paren_bind(X):
  | LPAREN xst=bind(X) RPAREN            { xst }

primarg:
  | LPAREN b=reduce xs=nonempty_list(name) COLON t=ty_term RPAREN  { List.map (fun x -> (x, b, t)) xs }

reduce:
  |          { false }
  | REDUCE { true }

(* function abstraction with possibly missing typing annotations *)
fun_abstraction:
  | xs=list(name) DARROW
      { (List.map (fun x -> (x, None)) xs) }
  | xs=nonempty_list(name) COLON t=ty_term DARROW
      { (List.map (fun x -> (x, Some t)) xs) }
  | xs=list(name) yst=paren_bind(ty_term) zsu=fun_abstraction
      { (List.map (fun x -> (x, None)) xs) @
        (List.map (fun (y,t) -> (y, Some t)) yst) @
         zsu
      }

mark_location(X):
  x=X
  { x, Location.make $startpos $endpos }

%%
