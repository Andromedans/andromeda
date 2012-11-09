%{
  open Syntax

  (* Build nested lambdas *)
  let rec make_lambda e = function
    | [] -> e
    | (xs, t) :: lst ->
      let e = make_lambda e lst in
        List.fold_left (fun e x -> Lambda (x, t, e)) e xs

  (* Build nested pies *)
  let rec make_pi e = function
    | [] -> e
    | (xs, t) :: lst ->
      let e = make_lambda e lst in
        List.fold_left (fun e x -> Pi (x, t, e)) e xs

%}

%token FORALL FUN TYPE
%token <int> NUMERAL
%token <string> NAME
%token LPAREN RPAREN
%token COLON COMMA PERIOD COLONEQUAL
%token ARROW DARROW
%token QUIT HELP PARAMETER CHECK EVAL CONTEXT DEFINITION
%token EOF

%start <Syntax.directive list> directives

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
  | DEFINITION x = NAME COLONEQUAL e = expr
    { Definition (String x, e) }
  | CONTEXT
    { Context }

(* Main syntax tree *)

expr:
  | e = app_expr
    { e }
  | FORALL lst = abstraction COMMA e = expr
    { make_pi e lst }
  | t1 = app_expr ARROW t2 = expr
    { Pi (Dummy, t1, t2) }
  | FUN lst = abstraction DARROW e = expr
    { make_lambda e lst }

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

abstraction:
  | b = bind1
    { [b] }
  | bs = binds
    { bs }

bind1:
  | xs = nonempty_list(NAME) COLON t = expr
    { (List.map (fun x -> String x) xs, t) }

binds:
  | LPAREN b = bind1 RPAREN
    { [b] }
  | LPAREN b = bind1 RPAREN lst = binds
    { b :: lst }

%%
