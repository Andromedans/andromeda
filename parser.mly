%{
  open Syntax
%}

%token LPAREN RPAREN SEMISEMI
%token FORALL FUN TYPE
%token <int> NUMERAL
%token <string> NAME
%token COLON COMMA ARROW DARROW
%token QUIT HELP ASSUME CONTEXT
%token EOF

%start <Syntax.toplevel list> file
%start <Syntax.toplevel> commandline

%%

(* Toplevel syntax *)

file:
  | e = expr EOF
     { [Expr e] }
  | e = expr SEMISEMI lst = file
     { (Expr e) :: lst }
  | dir = topdirective EOF
     { [Directive dir] }
  | dir = topdirective SEMISEMI lst = file
     { Directive dir :: lst }

commandline:
  | e = expr SEMISEMI
    { Expr e }
  | dir = topdirective SEMISEMI
    { Directive dir }

topdirective:
  | QUIT
    { Quit }
  | HELP
    { Help }
  | ASSUME x = NAME COLON e = expr
    { Assume (String x, e) }
  | CONTEXT
    { Context }

(* Main syntax tree *)

expr:
  | e = app_expr
    { e }
  | FORALL a = pi_abstraction
    { Pi a }
  | t1 = app_expr ARROW t2 = expr
    { Pi (Dummy, t1, t2) }
  | FUN a = fun_abstraction
    { Lambda a }

app_expr:
  | e = simple_expr
    { e }
  | e1 = app_expr e2 = simple_expr
    { App (e1, e2) }

simple_expr:
  | n = NAME
    { Var (String n) }
  | TYPE k = NUMERAL
    { Universe k }
  | LPAREN e = expr RPAREN
    { e }

pi_abstraction:
  | x = NAME COLON t = simple_expr COMMA e = expr
    { (String x, t, e) }

fun_abstraction:
  | x = NAME COLON t = simple_expr DARROW e = expr
    { (String x, t, e) }

%%
