%{
  open Input

  (* Build nested lambdas *)
  let rec make_lambda xs e =
    List.fold_right (fun (x, loc) e -> (Lambda (x, e), loc)) xs e

  (* Build nested pies *)
  let rec make_pi e = function
    | [] -> e
    | ((xs, t), loc) :: lst ->
      let e = make_pi e lst in
        List.fold_right (fun x e -> (Pi (x, t, e), loc)) xs e

%}

%token FORALL FUN TYPE
%token <int> NUMERAL
%token <string> NAME
%token LPAREN RPAREN
%token COLON DCOLON COMMA PERIOD COLONEQUAL
%token ARROW DARROW
%token QUIT HELP PARAMETER CHECK EVAL CONTEXT DEFINITION
%token EOF

%start <Input.directive list> directives

%%

(* Toplevel syntax *)

directives:
  | dir = directive PERIOD EOF
     { [dir] }
  | dir = directive PERIOD lst = directives
     { dir :: lst }

directive: mark_position(plain_directive) { $1 }
plain_directive:
  | QUIT
    { Quit }
  | HELP
    { Help }
  | PARAMETER x = NAME COLON e = expr
    { Parameter (x, e) }
  | CHECK e = expr
    { Check e }
  | EVAL e = expr
    { Eval e}
  | DEFINITION x = NAME COLONEQUAL e = expr
    { Definition (x, e) }
  | DEFINITION x = NAME DCOLON t = expr COLONEQUAL e = expr
    { Definition (x, (Ascribe (e, t), snd e)) }
  | CONTEXT
    { Context }

(* Main syntax tree *)
expr: mark_position(plain_expr) { $1 }
plain_expr:
  | e = plain_quantifier_expr
    { e }
  | e = quantifier_expr DCOLON t = quantifier_expr
    { Ascribe (e, t) }

quantifier_expr: mark_position(plain_quantifier_expr) { $1 }
plain_quantifier_expr:
  | e = plain_app_expr
    { e }
  | FORALL lst = pi_abstraction COMMA e = quantifier_expr
    { fst (make_pi e lst) }
  | t1 = app_expr ARROW t2 = quantifier_expr
    { Pi ("_", t1, t2) }
  | FUN lst = fun_abstraction DARROW e = quantifier_expr
    { fst (make_lambda lst e) }

app_expr: mark_position(plain_app_expr) { $1 }
plain_app_expr:
  | e = plain_simple_expr
    { e }
  | TYPE k = NUMERAL
    { Universe k }
  | e1 = app_expr e2 = simple_expr
    { App (e1, e2) }

simple_expr: mark_position(plain_simple_expr) { $1 }
plain_simple_expr:
  | n = NAME
    { Var n }
  | LPAREN e = plain_expr RPAREN
    { e }

pi_abstraction:
  | b = pi_bind1
    { [b] }
  | bs = pi_binds
    { bs }

pi_bind1: mark_position(plain_pi_bind1) { $1 }
plain_pi_bind1:
  | xs = nonempty_list(NAME) COLON t = expr
    { (xs, t) }

pi_binds:
  | LPAREN b = pi_bind1 RPAREN
    { [b] }
  | LPAREN b = pi_bind1 RPAREN lst = pi_binds
    { b :: lst }

fun_abstraction:
  | xs = nonempty_list(marked_name)
    { xs }

marked_name: mark_position(NAME) { $1 }

mark_position(X):
  x = X
  { x, Common.Position ($startpos, $endpos) }

%%
