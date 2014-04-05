%{
  open Input

  (* Build nested lambdas *)
  let rec make_lambda e = function
    | [] -> e
    | ((xs, t), pos) :: lst ->
      let e = make_lambda e lst in
        List.fold_right (fun x e -> (Lambda (x, t, e), pos)) xs e

  (* Build nested pi's *)
  let rec make_pi e = function
    | [] -> e
    | ((xs, None), pos) :: lst ->
      Error.syntax ~pos "missing type annotation in product"
    | ((xs, Some t), pos) :: lst ->
      let e = make_pi e lst in
        List.fold_right (fun x e -> (Prod (x, t, e), pos)) xs e

%}

%token FORALL FUN
%token <Universe.t> UNIVERSE
%token <string> NAME
%token LPAREN RPAREN
%token COLON ASCRIBE COMMA
%token ARROW DARROW
%token COERCE
%token EQ EQEQ AT
%token EQUATION REWRITE IN
%token REFL IDPATH
%token IND_EQ IND_PATH
%token UNDERSCORE
%token DECLARE CONTEXT QUIT
%token EOF

%start <Common.variable Input.toplevel list> file
%start <Common.variable Input.toplevel> commandline

%%

(* Toplevel syntax *)

file:
  | f = filecontents EOF            { f }

filecontents:
  |                                         { [] }
  | d = topdef sso ds = filecontents        { d :: ds }
  | d = topdirective sso ds = filecontents  { d :: ds }

commandline:
  | topdef SEMISEMI        { $1 }
  | topdirective SEMISEMI  { $1 }

(* Things that can be defined on toplevel. *)
topdef: mark_position(plain_topdef) { $1 }
plain_topdef:
  | DEFINE NAME COLONEQ expr               { TopDef ($2, None, $4) }
  | DEFINE NAME COLON expr COLONEQ expr    { TopDef ($2, Some $4, $6) }
  | ASSUME nonempty_list(NAME) COLON expr  { TopParam ($2, $4) }

(* Toplevel directive. *)
topdirective: mark_position(plain_topdirective) { $1 }
plain_topdirective:
  | CONTEXT    { Context }
  | HELP       { Help }
  | QUIT       { Quit }

sso :
  |          {}
  | SEMISEMI {}

(* Main syntax tree *)

expr: mark_position(plain_expr) { $1 }
plain_expr:
  | e = plain_arrow_expr                      { e }
  | FORALL a = abstraction COMMA  e = expr    { fst (make_pi e a) }
  | EXISTS a = abstraction COMMA  e = expr    { fst (make_sigma e a) }
  | FUN    a = abstraction DARROW e = expr    { fst (make_lambda e a) }
  | e1 = arrow_expr ASCRIBE e2 = expr         { Ascribe (e1, e2) }
  | EQUATION e1 = arrow_expr IN e2 = expr     { Equation (e1, e2) }
  | REWRITE e1 = arrow_expr IN e2 = expr      { Rewrite (e1, e2) }

arrow_expr: mark_position(plain_arrow_expr) { $1 }
plain_arrow_expr:
  | e = plain_equiv_expr                                { e }
  | e1 = equiv_expr ARROW e2 = arrow_expr               { Pi ("_", e1, e2) }
  | LPAREN x = NAME COLON e1 = expr RPAREN ARROW e2 = arrow_expr { Pi (x, e1, e2) }

equiv_expr: mark_position(plain_equiv_expr) { $1 }
plain_equiv_expr:
    | e = plain_app_expr                                { e }
    | e1 = app_expr EQEQ e2 = app_expr AT e3 = app_expr { Id (e1, e2, e3) }
    | e1 = app_expr EQ   e2 = app_expr AT e3 = app_expr { Paths (e1, e2, e3) }

app_expr: mark_position(plain_app_expr) { $1 }
plain_app_expr:
  | e = plain_simple_expr            { e }
  | e1 = app_expr e2 = simple_expr   { App (e1, e2) }
  | REFL e = simple_expr             { Refl e }
  | IDPATH e = simple_expr           { Idpath e }
  | IND LPAREN
          q = expr
        COMMA
          x = NAME DOT
          y = NAME DOT
          p = NAME DOT
          t = expr
        COMMA
          z = NAME DOT
          u = expr
        RPAREN
        { Ind((x, y, p, t), (z, u), q) }

simple_param_name:
  | NAME { $1 }
  | UNDERSCORE { "_" }

simple_expr: mark_position(plain_simple_expr) { $1 }
plain_simple_expr:
  | x = NAME                       { Var x }
  | UNIVERSE u = universe_index    { Universe u }
  | LPAREN e = plain_expr RPAREN   { e }

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
  | xs=nonempty_list(simple_param_name)             { (xs, None) }

annotated_var_list: mark_position(plain_annotated_var_list) { $1 }
plain_annotated_var_list:
  | xs=nonempty_list(simple_param_name) COLON expr  { (xs, Some $3) }

binds:
  | binds_leading_paren            { $1 }
  | unannotated_var_list              { [$1] }
  | unannotated_var_list binds_leading_paren { $1 :: $2 }

bind_leading_paren:
  | LPAREN simple_bind1 RPAREN           { $2 }

binds_leading_paren:
  | bind_leading_paren       { [$1] }
  | bind_leading_paren binds { $1 :: $2 }

mark_position(X):
  x = X
  { x, Common.Position ($startpos, $endpos) }

%%
