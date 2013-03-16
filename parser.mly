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

  (* Abstract a computation *)
  let make_computation lst c =
    let lst =
      List.fold_right
        (fun ((xs, t), loc) lst -> List.fold_right (fun x c -> ((x, t), loc) :: lst) xs lst)
        lst
        []
    in
      (lst, c)

%}

%token FORALL FUN TYPE
(* %token <int> NUMERAL *)
%token <string> NAME
%token LPAREN RPAREN
%token COLON DCOLON COMMA QUESTIONMARK SEMISEMI VDASH
%token ARROW DARROW
%token EQ EQEQ AT
%token LET
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
  | LET x = NAME EQ c = computation
    { TopLet (x, c) }
  | LET x = NAME COLON s = sort
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
  | lst = pi_abstraction VDASH j = operation
    { make_computation lst j }

operation: mark_position(plain_operation) { $1 }
plain_operation:
  | QUESTIONMARK DCOLON s = sort
    { Inhabit s }
  | e = expr DCOLON QUESTIONMARK
    { Infer e }
  | e = expr DCOLON s = sort
    { HasType (e, s) }
  | e1 = expr EQEQ e2 = expr AT s = sort
    { Equal (e1, e2, s) }

sort: expr { $1 }

expr: mark_position(plain_expr) { $1 }
plain_expr:
  | e = plain_app_expr
    { e }
  | FORALL lst = pi_abstraction COMMA e = expr
    { fst (make_pi e lst) }
  | t1 = app_expr ARROW t2 = expr
    { Pi ("_", t1, t2) }
  | FUN lst = fun_abstraction DARROW e = expr
    { fst (make_lambda e lst) }
  | e1 = app_expr EQ e2 = app_expr AT t = expr
    { EqJdg (e1, e2, t) }
  | e = app_expr DCOLON t = expr
    { TyJdg (e, t) }
  | e = expr COLON t = expr
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
