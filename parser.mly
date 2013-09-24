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
%token <int> NUMERAL
%token <string> NAME
%token LPAREN RPAREN LBRACK RBRACK
%token COLON DCOLON COMMA QUESTIONMARK SEMISEMI
%token ARROW DARROW
%token EQ COLONEQ EQEQ AT
%token REFL TRANSPORT
%token NAT SUCC NATREC
%token DEFINE LET IN ASSUME
%token HANDLE WITH BAR END RETURN
%token QUIT HELP EVAL CONTEXT
%token EOF

%start <Input.toplevel list> file
%start <Input.toplevel> commandline

%%

(* Toplevel syntax *)

(* If you're going to "optimize" this, please make sure we don't require;; at the
   end of the file. *)
file:
  | file_topdef                 { $1 }
  | topcomp EOF                 { [$1] }
  | topcomp SEMISEMI file       { $1 :: $3 }
  | topdirective EOF            { [$1] }
  | topdirective SEMISEMI file  { $1 :: $3 }

file_topdef:
  | EOF                   { [] }
  | topdef SEMISEMI file  { $1 :: $3 }
  | topdef file_topdef    { $1 :: $2 }

commandline:
  | topdef SEMISEMI        { $1 }
  | topcomp SEMISEMI       { $1 }
  | topdirective SEMISEMI  { $1 }

topcomp: mark_position(plain_topcomp) { $1 }
plain_topcomp:
  |  computation  { Computation $1 }

(* Things that can be defined on toplevel. *)
topdef: mark_position(plain_topdef) { $1 }
plain_topdef:
  | DEFINE NAME COLONEQ expr               { TopDefine ($2, $4) }
  | ASSUME nonempty_list(NAME) COLON expr  { TopParam ($2, $4) }
  | LET NAME COLONEQ computation           { TopLet ($2, $4) }

(* Toplevel directive. *)
topdirective: mark_position(plain_topdirective) { $1 }
plain_topdirective:
  | CONTEXT    { Context }
  | EVAL expr  { Eval $2 }
  | HELP       { Help }
  | QUIT       { Quit }

(* Main syntax tree *)

computation: mark_position(plain_computation) { $1 }
plain_computation:
  | RETURN expr                                  { Return $2 }
  | LPAREN plain_computation RPAREN              { $2 }
  | FUN pi_abstraction DARROW computation        { fst (make_computation $4 $2) }
  | LBRACK operation RBRACK                      { Operation $2 }
  | HANDLE computation WITH handler END          { Handle ($2, $4) }
  | LET NAME COLONEQ computation IN computation  { Let ($2, $4, $6) }

operation: mark_position(plain_operation) { $1 }
plain_operation:
  | QUESTIONMARK DCOLON quant_expr        { Inhabit $3 }
  | quant_expr DCOLON QUESTIONMARK        { Infer $1 }
  | quant_expr DCOLON quant_expr          { HasType ($1, $3) }
  | app_expr EQEQ app_expr AT quant_expr  { Equal ($1, $3, $5) }

handler:
  | BAR? cs=separated_list(BAR, handler_case)  { cs }

handler_case:
  | LBRACK app_expr EQEQ app_expr AT quant_expr RBRACK DARROW computation
                                            { ($2, $4, $6, $9) }

expr: mark_position(plain_expr) { $1 }
plain_expr:
  | plain_quant_expr              { $1 }
  | quant_expr DCOLON quant_expr  { TyJdg ($1, $3) }

quant_expr: mark_position(plain_quant_expr) { $1 }
plain_quant_expr:
  | plain_app_expr                          { $1 }
  | app_expr EQEQ app_expr AT quant_expr    { EqJdg ($1, $3, $5) }
  | app_expr EQ app_expr AT quant_expr      { Id ($1, $3, $5) }
  | app_expr ARROW quant_expr               { Pi ("_", $1, $3) }
  | app_expr COLON quant_expr               { Ascribe ($1, $3) }
  | FORALL pi_abstraction COMMA quant_expr  { fst (make_pi $4 $2) }
  | FUN fun_abstraction DARROW quant_expr   { fst (make_lambda $4 $2) }

app_expr: mark_position(plain_app_expr) { $1 }
plain_app_expr:
  | plain_simple_expr                              { $1 }
  | REFL simple_expr                               { Refl $2 }
  | TRANSPORT simple_expr simple_expr simple_expr  { Transport ($2, $3, $4) }
  | SUCC simple_expr                               { Succ $2 }
  | NATREC simple_expr simple_expr simple_expr     { NatRec ($2, $3, $4) }
  | app_expr simple_expr                           { App ($1, $2) }

simple_expr: mark_position(plain_simple_expr) { $1 }
plain_simple_expr:
  | TYPE                      { Type }
  | NAT                       { Nat }
  | NUMERAL                   { Numeral $1 }
  | NAME                      { Var $1 }
  | LPAREN plain_expr RPAREN  { $2 }

pi_abstraction:
  | pi_bind1  { [$1] }
  | pi_binds  { $1 }

pi_bind1: mark_position(plain_pi_bind1) { $1 }
plain_pi_bind1:
  | xs=nonempty_list(NAME) COLON expr  { (xs, $3) }

pi_binds:
  | LPAREN pi_bind1 RPAREN           { [$2] }
  | LPAREN pi_bind1 RPAREN pi_binds  { $2 :: $4 }

fun_abstraction:
  | fun_bind1  { [$1] }
  | fun_binds  { $1 }

fun_bind1: mark_position(plain_fun_bind1) { $1 }
plain_fun_bind1:
  | xs=nonempty_list(NAME)             { (xs, None) }
  | xs=nonempty_list(NAME) COLON expr  { (xs, Some $3) }

fun_binds:
  | LPAREN fun_bind1 RPAREN            { [$2] }
  | LPAREN fun_bind1 RPAREN fun_binds  { $2 :: $4 }

mark_position(X):
  x = X
  { x, Common.Position ($startpos, $endpos) }

%%
