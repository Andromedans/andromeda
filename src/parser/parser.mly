%{
  open Input
%}

%token FORALL FUN
%token TYPE
%token UNDERSCORE
%token <string> NAME
%token LPAREN RPAREN LBRACK RBRACK
%token COLON SEMICOLON COMMA DOT
%token ARROW DARROW
%token EQEQ
%token REFL
%token TOPLET TOPCHECK TOPBETA TOPETA TOPHINT TOPINHABIT
%token TOPUNHINT
%token LET COLONEQ AND IN
%token BETA ETA HINT INHABIT
%token UNHINT
%token WHNF
%token PRIMITIVE REDUCE
%token CONTEXT HELP QUIT
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
  | TOPLET x=name yts=paren_bind(ty_term)* u=return_type? COLONEQ c=term DOT
      { let yts = List.flatten yts in TopLet (x, yts, u, c) }
  | TOPCHECK c=term DOT                                  { TopCheck c }
  | TOPBETA ths=tags_hints DOT                           { TopBeta ths }
  | TOPETA ths=tags_hints DOT                            { TopEta ths }
  | TOPHINT ths=tags_hints DOT                           { TopHint ths }
  | TOPINHABIT ths=tags_hints DOT                        { TopInhabit ths }
  | TOPUNHINT ts=tags_unhints DOT                        { TopUnhint ts }
  | PRIMITIVE xs=name+ yst=primarg* COLON u=term DOT     { Primitive (xs, List.concat yst, u)}

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
  | WHNF t=term                                     { Whnf t }
  | LET a=let_clauses IN c=term                     { Let (a, c) }
  | BETA tshs=tags_opt_hints IN c=term              { Beta (tshs, c) }
  | ETA tshs=tags_opt_hints IN c=term               { Eta (tshs, c) }
  | HINT tshs=tags_opt_hints IN c=term              { Hint (tshs, c) }
  | INHABIT tshs=tags_opt_hints IN c=term           { Inhabit (tshs, c) }
  | UNHINT ts=tags_unhints IN c=term                { Unhint (ts, c) }
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

mark_location(X):
  x=X
  { x, Location.make $startpos $endpos }
%%
