%{
  open Input

  (* Build nested lambdas *)
  let rec make_lambda e = function
    | [] -> e
    | ((xs, t), loc) :: lst ->
      let e = make_lambda e lst in
        List.fold_right (fun x e -> (Lambda (x, t, e), loc)) xs e

  (* Build nested pi's *)
  let rec make_pi e = function
    | [] -> e
    | ((xs, None), loc) :: lst ->
      Error.syntax ~loc "missing type annotation in product"
    | ((xs, Some t), loc) :: lst ->
      let e = make_pi e lst in
        List.fold_right (fun x e -> (Prod (x, t, e), loc)) xs e

%}

%token FORALL FUN
%token <Universe.t> UNIVERSE
%token <string> NAME
%token LPAREN RPAREN LBRACK RBRACK
%token COLON ASCRIBE COMMA DOT
%token ARROW DARROW
%token COERCE
%token EQ EQEQ AT
%token EQUATION REWRITE IN
%token REFL IDPATH
%token IND_EQ IND_PATH
%token UNDERSCORE
%token DEFINE COLONEQ ASSUME
%token CONTEXT HELP QUIT
%token EOF

%start <Common.variable Input.toplevel list> file
%start <Common.variable Input.toplevel> commandline

%%

(* Toplevel syntax *)

file:
  | f=filecontents EOF            { f }

filecontents:
  |                                 { [] }
  | d=topdef ds=filecontents        { d :: ds }
  | d=topdirective ds=filecontents  { d :: ds }

commandline:
  | topdef        { $1 }
  | topdirective  { $1 }

(* Things that can be defined on toplevel. *)
topdef: mark_position(plain_topdef) { $1 }
plain_topdef:
  | DEFINE NAME COLONEQ expr               { Define ($2, None, $4) }
  | DEFINE NAME COLON expr COLONEQ expr    { Define ($2, Some $4, $6) }
  | ASSUME nonempty_list(NAME) COLON expr  { Assume ($2, $4) }

(* Toplevel directive. *)
topdirective: mark_position(plain_topdirective) { $1 }
plain_topdirective:
  | CONTEXT    { Context }
  | HELP       { Help }
  | QUIT       { Quit }

(* Main syntax tree *)

expr: mark_position(plain_expr) { $1 }
plain_expr:
  | e=plain_arrow_expr                    { e }
  | FORALL a=abstraction COMMA  e=expr    { fst (make_pi e a) }
  | FUN    a=abstraction DARROW e=expr    { fst (make_lambda e a) }
  | e1=arrow_expr ASCRIBE e2=expr         { Ascribe (e1, e2) }
  | EQUATION e1=arrow_expr IN e2=expr     { Equation (e1, e2) }
  | REWRITE e1=arrow_expr IN e2=expr      { Rewrite (e1, e2) }

arrow_expr: mark_position(plain_arrow_expr) { $1 }
plain_arrow_expr:
  | e=plain_equiv_expr                                     { e }
  | e1=equiv_expr ARROW e2=arrow_expr                      { Prod (anonymous, e1, e2) }
  | LPAREN x=NAME COLON e1=expr RPAREN ARROW e2=arrow_expr { Prod (x, e1, e2) }

equiv_expr: mark_position(plain_equiv_expr) { $1 }
plain_equiv_expr:
    | e=plain_app_expr                                     { e }
    | e1=app_expr EQEQ e2=app_expr AT e3=app_expr          { Id (e1, e2, e3) }
    | e1=app_expr EQ   e2=app_expr AT e3=app_expr          { Paths (e1, e2, e3) }

app_expr: mark_position(plain_app_expr) { $1 }
plain_app_expr:
  | e=plain_simple_expr             { e }
  | e1=app_expr e2=simple_expr      { App (e1, e2) }
  | COERCE u=universe_index e=expr  { Coerce (u, e) }
  | REFL e=simple_expr              { Refl e }
  | IDPATH e=simple_expr            { Idpath e }
  | IND_PATH LPAREN
          q=expr
        COMMA
          LBRACK
          x=NAME DOT
          y=NAME DOT
          p=NAME DOT
          t=expr
          RBRACK
        COMMA
          LBRACK
          z=NAME DOT
          u=expr
          RBRACK
        RPAREN
                                    { J (q, (x, y, p, t), (z, u)) }
  | IND_EQ LPAREN
          q=expr
        COMMA
          x=NAME DOT
          y=NAME DOT
          p=NAME DOT
          t=expr
        COMMA
          z=NAME DOT
          u=expr
        RPAREN
                                    { G (q, (x, y, p, t), (z, u)) }

simple_param_name:
  | NAME { $1 }
  | UNDERSCORE { anonymous }

simple_expr: mark_position(plain_simple_expr) { $1 }
plain_simple_expr:
  | x=NAME                       { Var x }
  | UNIVERSE u=universe_index    { Universe u }
  | LPAREN e=plain_expr RPAREN   { e }

universe_index: mark_position(plain_universe_index) { $1 }
plain_universe_index:
  | LBRACK u=NAME RBRACK         { u }

(* returns a list of things individually annotated by positions.
  Since the list is not further annotated, consistency suggests
  this should be called plain_abstraction, but as we know,
  consistency is the hemoglobin of mindless lights. *)
abstraction:
  | annotated_var_list  { [$1] }
  | binds               { $1 }

simple_bind1: mark_position(plain_simple_bind1) { $1 }
plain_simple_bind1:
    | plain_unannotated_var_list  { $1 }
    | plain_annotated_var_list    { $1 }

unannotated_var_list: mark_position(plain_unannotated_var_list) { $1 }
plain_unannotated_var_list:
  | xs=nonempty_list(simple_param_name)                { (xs, None) }

annotated_var_list: mark_position(plain_annotated_var_list) { $1 }
plain_annotated_var_list:
  | xs=nonempty_list(simple_param_name) COLON t=expr   { (xs, Some t) }

binds:
  | b=binds_leading_paren                            { b }
  | xs=unannotated_var_list                          { [xs] }
  | xs=unannotated_var_list bs=binds_leading_paren   { xs :: bs }

bind_leading_paren:
  | LPAREN b=simple_bind1 RPAREN                     { b }

binds_leading_paren:
  | b=bind_leading_paren                             { [b] }
  | b=bind_leading_paren bs=binds                    { b :: bs }

mark_position(X):
  x=X
  { x, Common.Position ($startpos, $endpos) }

%%
