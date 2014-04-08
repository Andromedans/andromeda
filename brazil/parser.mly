%{
  open Input

  (* Build nested lambdas *)
  let make_lambda e u bs =
    let rec make u e = function
      | [] -> u, e
      | ((xs, t), loc) :: lst ->
        let u, e = make e u lst in
          List.fold_right
            (fun x (u, e) ->
              ((Prod (x, t, u), loc), (Lambda (x, t, u, e), loc)))
            xs
            (u, e)
    in
      snd (make u e bs)

  (* Build nested pi's *)
  let rec make_pi e = function
    | [] -> e
    | ((xs, t), loc) :: lst ->
      let e = make_pi e lst in
        List.fold_right (fun x e -> (Prod (x, t, e), loc)) xs e

  let make_universe (u, loc) =
    match Universe.of_string u with
      | None -> Error.syntax "invalid universe index %s" u
      | Some u -> (u, loc)

%}

%token FORALL FUN
%token UNIVERSE UNIT
%token <string> NAME
%token LPAREN RPAREN LBRACK RBRACK
%token COLON ASCRIBE COMMA DOT
%token ARROW DARROW
%token COERCE
%token EQ EQEQ AT
%token EQUATION REWRITE IN
%token REFL IDPATH
%token IND_PATH
%token UNDERSCORE
%token DEFINE COLONEQ ASSUME
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
  | d=topdef ds=filecontents        { d :: ds }
  | d=topdirective ds=filecontents  { d :: ds }

commandline:
  | topdef EOF       { $1 }
  | topdirective EOF { $1 }

(* Things that can be defined on toplevel. *)
topdef: mark_position(plain_topdef) { $1 }
plain_topdef:
  | DEFINE x=NAME COLON t=expr COLONEQ e=expr   { Define (x, t, e) }
  | ASSUME xs=nonempty_list(NAME) COLON t=expr  { Assume (xs, t) }

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
  | FUN    a=abstraction DARROW LBRACK u=expr RBRACK e=expr
                                          { fst (make_lambda u e a) }
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
    | e1=app_expr EQEQ LBRACK e3=expr RBRACK e2=app_expr   { Id (e1, e2, e3) }
    | e1=app_expr EQ LBRACK e3=expr RBRACK e2=app_expr     { Paths (e1, e2, e3) }

app_expr: mark_position(plain_app_expr) { $1 }
plain_app_expr:
  | e=plain_simple_expr                       { e }
  | e1=app_expr
    AT LBRACK x=param COLON t1=equiv_expr DOT t2=expr RBRACK
    e2=simple_expr
                                              { App ((x, t1, t2), e1, e2) }
  | COERCE LPAREN u1=universe COMMA u2=universe COMMA e=expr RPAREN
                                              { let u1 = make_universe u1 in
                                                let u2 = make_universe u2 in
                                                  Coerce (u1, u2, e) }
  | UNIVERSE u=universe                       { let u = make_universe u in
                                                  Universe u }
  | REFL LBRACK t=expr RBRACK e=simple_expr   { Refl (t, e) }
  | IDPATH LBRACK t=expr RBRACK e=simple_expr { Idpath (t, e) }
  | IND_PATH LPAREN
          t=expr
        COMMA
          LBRACK
          x=param
          y=param
          p=param DOT
          u=expr
          RBRACK
        COMMA
          LBRACK
          z=param DOT
          e1=expr
          RBRACK
        COMMA
          e2=expr
        COMMA
          e3=expr
        COMMA
          e4=expr
        RPAREN
                                              { J (t, (x, y, p, u), (z, e1), e2, e3, e4) }

param:
  | NAME { $1 }
  | UNDERSCORE { anonymous }

simple_expr: mark_position(plain_simple_expr) { $1 }
plain_simple_expr:
  | UNIT                         { Unit }
  | x=NAME                       { Var x }
  | LPAREN e=plain_expr RPAREN   { e }

universe: mark_position(plain_universe) { $1 }
plain_universe:
  | u=NAME { u }

(* returns a list of things individually annotated by positions.
  Since the list is not further annotated, consistency suggests
  this should be called plain_abstraction, but as we know,
  consistency is the hemoglobin of mindless lights. *)
abstraction:
  | bind   { [$1] }
  | nonempty_list(paren_bind)  { $1 }

bind: mark_position(plain_bind) { $1 }
plain_bind:
  | xs=nonempty_list(param) COLON t=expr   { (xs, t) }

paren_bind:
  | LPAREN b=bind RPAREN               { b }

mark_position(X):
  x=X
  { x, Position.make $startpos $endpos }

%%
