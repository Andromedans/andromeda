%{
  open Input

  (* Build nested lambdas *)
  let rec make_lambda e = function
    | [] -> e
    | ((xs, t), loc) :: lst ->
      let e = make_lambda e lst in
        List.fold_right (fun x e -> (Lambda (x, t, e), loc)) xs e

  (* Build nested pies *)
  let rec make_pi e = function
    | [] -> e
    | ((xs, t), loc) :: lst ->
      let e = make_pi e lst in
        List.fold_right (fun x e -> (Pi (x, t, e), loc)) xs e

  (* Build nested pies *)
  let rec make_computation c = function
    | [] -> c
    | ((xs, t), loc) :: lst ->
      let c = make_computation c lst in
        List.fold_right (fun x c -> (Abstraction (x, t, c), loc)) xs c
%}

%token FORALL FUN TYPE
(* %token <int> NUMERAL *)
%token <string> NAME
%token LPAREN RPAREN LBRACK RBRACK
%token COLON DCOLON COMMA QUESTIONMARK SEMISEMI
%token ARROW DARROW
%token COLONEQ EQEQ AT
%token LET ASSUME
%token HANDLE WITH BAR
%token QUIT HELP EVAL CONTEXT
%token EOF

%start <Input.toplevel list> file
%start <Input.toplevel> commandline

%%

(* Toplevel syntax *)

(* If you're going to "optimize" this, please make sure we don't require;; at the
   end of the file. *)
file:
  | lst = file_topdef
    { lst }
  | c = topcomp EOF
     { [c] }
  | c = topcomp SEMISEMI lst = file
     { c :: lst }
  | dir = topdirective EOF
     { [dir] }
  | dir = topdirective SEMISEMI lst = file
     { dir :: lst }

file_topdef:
  | EOF
     { [] }
  | def = topdef SEMISEMI lst = file
     { def :: lst }
  | def = topdef lst = file_topdef
     { def :: lst }

commandline:
  | def = topdef SEMISEMI
    { def }
  | c = topcomp SEMISEMI
    { c }
  | dir = topdirective SEMISEMI
    { dir }

topcomp: mark_position(plain_topcomp) { $1 }
plain_topcomp:
  | c = computation
    { Computation c }

(* Things that can be defined on toplevel. *)
topdef: mark_position(plain_topdef) { $1 }
plain_topdef:
  | LET x = NAME COLONEQ e = expr
    { TopLet (x, e) }
  | ASSUME x = NAME COLON s = expr
    { TopParam (x, s) }

(* Toplevel directive. *)
topdirective: mark_position(plain_topdirective) { $1 }
plain_topdirective:
  | CONTEXT
    { Context }
  | EVAL e = expr
    { Eval e }
  | HELP
    { Help }
  | QUIT
    { Quit }

(* Main syntax tree *)

computation: mark_position(plain_computation) { $1 }
plain_computation:
  | FUN lst = pi_abstraction DARROW c = computation
    { fst (make_computation c lst) }
  | LBRACK op = operation RBRACK
    { Operation op }
  | HANDLE c = computation WITH h = handler
    { Handle (c, h) }

operation: mark_position(plain_operation) { $1 }
plain_operation:
  | QUESTIONMARK DCOLON s = quant_expr
    { Inhabit s }
  | e = quant_expr DCOLON QUESTIONMARK
    { Infer e }
  | e = quant_expr DCOLON s = quant_expr
    { HasType (e, s) }
  | e1 = quant_expr EQEQ e2 = quant_expr AT s = quant_expr
    { Equal (e1, e2, s) }

handler:
  | BAR? cs = separated_list(BAR, handler_case)
    { cs }

handler_case:
  | LBRACK e1 = quant_expr EQEQ e2 = quant_expr AT s = quant_expr RBRACK DARROW e = expr
    { (e1, e2, s, e) }

expr: mark_position(plain_expr) { $1 }
plain_expr:
  | e = plain_quant_expr
    { e }
  | e1 = quant_expr EQEQ e2 = quant_expr AT t = quant_expr
    { EqJdg (e1, e2, t) }
  | e = quant_expr DCOLON t = quant_expr
    { TyJdg (e, t) }

quant_expr: mark_position(plain_quant_expr) { $1 }
plain_quant_expr:
  | e = plain_app_expr
    { e }
  | FORALL lst = pi_abstraction COMMA e = quant_expr
    { fst (make_pi e lst) }
  | t1 = app_expr ARROW t2 = quant_expr
    { Pi ("_", t1, t2) }
  | FUN lst = fun_abstraction DARROW e = quant_expr
    { fst (make_lambda e lst) }
  | e = app_expr COLON t = app_expr
    { Ascribe (e, t) }

app_expr: mark_position(plain_app_expr) { $1 }
plain_app_expr:
  | e = plain_simple_expr
    { e }
  | e1 = app_expr e2 = simple_expr
    { App (e1, e2) }

simple_expr: mark_position(plain_simple_expr) { $1 }
plain_simple_expr:
  | TYPE
    { Type }
  | x = NAME
    { Var x }
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
  | b = fun_bind1
    { [b] }
  | bs = fun_binds
    { bs }

fun_bind1: mark_position(plain_fun_bind1) { $1 }
plain_fun_bind1:
  | xs = nonempty_list(NAME)
    { (xs, None) }
  | xs = nonempty_list(NAME) COLON t = expr
    { (xs, Some t) }

fun_binds:
  | LPAREN b = fun_bind1 RPAREN
    { [b] }
  | LPAREN b = fun_bind1 RPAREN lst = fun_binds
    { b :: lst }

mark_position(X):
  x = X
  { x, Common.Position ($startpos, $endpos) }

%%
