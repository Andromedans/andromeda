%{
  open Concrete
%}

%token FORALL FUN TYPE
%token <int> NUMERAL
%token <string> NAME
%token LPAREN RPAREN
%token COLON COMMA PERIOD
%token ARROW DARROW
%token QUIT HELP PARAMETER CHECK EVAL CONTEXT
%token EOF

%start <Concrete.directive list> directives

%%

(* Toplevel syntax *)

directives:
  | dir = directive PERIOD EOF
     { [dir] }
  | dir = directive PERIOD lst = directives
     { dir :: lst }

directive:
  | QUIT
    { Quit }
  | HELP
    { Help }
  | PARAMETER x = NAME COLON e = expr
    { Parameter (String x, e) }
  | CHECK e = expr
    { Check e }
  | EVAL e = expr
    { Eval e}
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
  | x = NAME COLON t = expr COMMA e = expr
    { (String x, t, e) }

fun_abstraction:
  | x = NAME COLON t = expr DARROW e = expr
    { (String x, t, e) }

%%
