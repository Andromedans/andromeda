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
        List.fold_right (fun x e -> (NameProd (x, t, e), loc)) xs e

  let make_universe (u, loc) =
    match Universe.of_string u with
      | None -> Error.syntax ~loc "invalid universe index %s" u
      | Some u -> u

%}

%token FORALL FUN
%token UNIVERSE UNIT
%token <string> NAME
%token LPAREN RPAREN LBRACK RBRACK
%token COLON ASCRIBE COMMA DOT
%token ARROW DARROW
%token COERCE
%token EQ EQEQ
%token EQUATION REWRITE IN
%token AS LBRACE RBRACE SEMICOLON
%token <string> PROJECT
%token REFL IDPATH
%token IND_PATH
%token UNDERSCORE
%token DEFINE COLONEQ ASSUME TOPEQUATION TOPREWRITE
%token CONTEXT HELP QUIT
%token <int> VERBOSE
%token EOF

%start <Input.toplevel list> file
%start <Input.toplevel> commandline
%start <Common.name Input.term> topterm
%start <Common.name Input.ty> topty

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

topterm:
  | term EOF { $1 }

topty:
  | ty EOF { $1 }

(* Things that can be defined on toplevel. *)
topdef: mark_position(plain_topdef) { $1 }
plain_topdef:
  | DEFINE x=NAME COLONEQ e=term DOT             { Define (x, e) }
  | DEFINE x=NAME COLON t=ty COLONEQ e=term DOT  { Define (x, (Ascribe(e,t), snd e)) }
  | ASSUME xs=nonempty_list(NAME) COLON t=ty DOT { Assume (xs, t) }
  | TOPREWRITE e=term DOT                        { TopRewrite e }
  | TOPEQUATION e=term DOT                       { TopEquation e }

(* Toplevel directive. *)
topdirective: mark_position(plain_topdirective) { $1 }
plain_topdirective:
  | CONTEXT    { Context }
  | HELP       { Help }
  | QUIT       { Quit }
  | n=VERBOSE    { Verbose n }

(* Main syntax tree *)

term: mark_position(plain_term) { $1 }
plain_term:
  | e=plain_equal_term                              { e }
  | FORALL a=abstraction(term) COMMA  e=term        { fst (make_prod e a) }
  | FUN a=abstraction(ty) DARROW e=term             { fst (make_lambda e a) }
  | e=equal_term ASCRIBE t=ty                       { Ascribe (e, t) }
  | EQUATION e1=equal_term IN e2=term               { Equation (e1, e2) }
  | REWRITE e1=equal_term IN e2=term                { Rewrite (e1, e2) }
  | t1=equal_term ARROW t2=term                     { NameProd (anonymous, t1, t2) }
  | LPAREN x=param COLON t=term RPAREN ARROW e=term { NameProd (x, t, e) }

equal_term: mark_position(plain_equal_term) { $1 }
plain_equal_term:
    | e=plain_app_term               { e }
    | e1=app_term EQEQ e2=app_term   { NameId (e1, e2) }
    | e1=app_term EQ e2=app_term     { NamePaths (e1, e2) }

app_term: mark_position(plain_app_term) { $1 }
plain_app_term:
  | e=plain_project_term                          { e }
  | e1=app_term e2=project_term                   { App (e1, e2) }
  | COERCE LPAREN ul=universe COMMA e=term RPAREN { let u = make_universe ul in Coerce (u, e) }
  | UNIVERSE ul=universe                          { let u = make_universe ul in NameUniverse u }
  | REFL e=simple_term                            { Refl e }
  | IDPATH e=simple_term                          { Idpath e }
  | IND_PATH LPAREN
          LBRACK
          x=param
          y=param
          p=param DOT
          u=ty
          RBRACK
        COMMA
          LBRACK
          z=param DOT
          e1=term
          RBRACK
        COMMA
          e2=term
        RPAREN
                                              { J ((x, y, p, u), (z, e1), e2) }

param:
  | NAME { $1 }
  | UNDERSCORE { anonymous }

project_term: mark_position(plain_project_term) { $1 }
plain_project_term:
  | e=plain_simple_term           { e }
  | e=project_term lbl=PROJECT    { Project (e, lbl) }

simple_term: mark_position(plain_simple_term) { $1 }
plain_simple_term:
  | UNIT                         { NameUnit }
  | x=NAME                       { Var x }
  | LPAREN RPAREN                { UnitTerm }
  | LPAREN e=plain_term RPAREN   { e }
  | LBRACE l=separated_nonempty_list(SEMICOLON, record_field) RBRACE { Record l }
  | LBRACE l=separated_nonempty_list(SEMICOLON, record_ty_field) RBRACE { NameRecordTy l }

record_field:
  | lbl=NAME EQ e=term            { (lbl, anonymous, e) }
  | lbl=NAME AS x=param EQ e=term { (lbl, x, e) }

record_ty_field:
  | lbl=NAME COLON t=term              { (lbl, anonymous, t) }
  | lbl=NAME AS x=param COLON t=term   { (lbl, x, t) }

universe: mark_position(plain_universe) { $1 }
plain_universe:
  | u=NAME { u }

ty:
  | t=term { let (_,loc) = t in (El t, loc) }

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
