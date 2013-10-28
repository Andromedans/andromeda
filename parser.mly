%{
  open Input

  (* Build nested lambdas *)
  let rec make_lambda e = function
    | [] -> e
    | ((xs, t), loc) :: lst ->
      let e = make_lambda e lst in
        List.fold_right (fun x e -> (Lambda (x, t, e), loc)) xs e

  (* Build nested pi's *)
  let rec make_pi e = function
    | [] -> e
    | ((xs, t), loc) :: lst ->
      let e = make_pi e lst in
        List.fold_right (fun x e -> (Pi (x, t, e), loc)) xs e

%}

%token FORALL FUN TYPE
%token <string> NAME
%token LPAREN RPAREN LBRACK RBRACK
%token COLON DCOLON ASCRIBE COMMA QUESTIONMARK SEMISEMI
%token ARROW DARROW STAR
%token DOT1 DOT2
%token COLONEQ
(* %token EQEQ AT EVAL *)
%token DEFINE LET IN ASSUME
%token HANDLE WITH BAR END RETURN
%token QUIT HELP  CONTEXT
%token EOF


%start <Input.toplevel list> file
%start <Input.toplevel> commandline


%%

(* Toplevel syntax *)

(* If you're going to "optimize" this, please make sure we don't require;; at the
   end of the file. *)
file:
  | file_topdef                 { $1 }
  | topdirective EOF            { [$1] }
  | topdirective SEMISEMI file  { $1 :: $3 }

file_topdef:
  | EOF                   { [] }
  | topdef SEMISEMI file  { $1 :: $3 }
  | topdef file_topdef    { $1 :: $2 }

commandline:
  | topdef SEMISEMI        { $1 }
  | topdirective SEMISEMI  { $1 }

(* Things that can be defined on toplevel. *)
topdef: mark_position(plain_topdef) { $1 }
plain_topdef:
  | DEFINE NAME COLONEQ term               { TopDef ($2, $4) }
  | ASSUME nonempty_list(NAME) COLON term  { TopParam ($2, $4) }

(* Toplevel directive. *)
topdirective: mark_position(plain_topdirective) { $1 }
plain_topdirective:
  | CONTEXT    { Context }
  | HELP       { Help }
  | QUIT       { Quit }

(* Main syntax tree *)


term: mark_position(plain_term) { $1 }
plain_term:
  | plain_arrow_term                    { $1 }
  | FORALL pi_abstraction COMMA term  { fst (make_pi $4 $2) }
  | FUN fun_abstraction DARROW term   { fst (make_lambda $4 $2) }

arrow_term: mark_position(plain_arrow_term) { $1 }
plain_arrow_term:
  | plain_app_term              { $1 }
  | app_term ARROW arrow_term   { Pi ("_", $1, $3) }
  | LPAREN NAME COLON term RPAREN ARROW arrow_term      { Pi($2, $4, $7) }
  | LPAREN NAME COLON term RPAREN STAR arrow_term      { Sigma($2, $4, $7) }

app_term: mark_position(plain_app_term) { $1 }
plain_app_term:
  | plain_simple_term      { $1 }
  | app_term simple_term   { App ($1, $2) }


simple_term: mark_position(plain_simple_term) { $1 }
plain_simple_term:
  | NAME                           { Var $1 }
  | TYPE                           { Type }
  | LPAREN plain_term RPAREN       { $2 }
  | LPAREN term COMMA term RPAREN  { Pair($2, $4) }
  | LPAREN term ASCRIBE term RPAREN    { Ascribe ($2, $4) }
  | LBRACK plain_operation RBRACK        { let (tag,args) = $2 in Operation(tag,args) }
  | HANDLE term WITH handler END   { Handle ($2, $4) }
  | simple_term DOT1         { Proj(1, $1) }
  | simple_term DOT2         { Proj(2, $1) }

handler:
  | BAR? cs=separated_list(BAR, handler_case)  { cs }

handler_case:
  | LBRACK plain_operation RBRACK DARROW computation
                                            { let (tag,args) = $2 in (tag,args, $5) }

(*
computation: mark_position(plain_computation) { $1 }
plain_computation:
  | RETURN term                                  { Return $2 }
  | LPAREN plain_computation RPAREN              { $2 }
  | LET NAME COLONEQ term IN computation         { Let ($2, $4, $6) }
  *)
computation: term { $1 }

(*operation: mark_position(plain_operation) { $1 }*)
plain_operation:
    | QUESTIONMARK DCOLON term        { (Inhabit, [$3]) }

pi_abstraction:
  | pi_bind1  { [$1] }
  | pi_binds  { $1 }

pi_bind1: mark_position(plain_pi_bind1) { $1 }
plain_pi_bind1:
  | xs=nonempty_list(NAME) COLON term  { (xs, $3) }

pi_binds:
  | LPAREN pi_bind1 RPAREN           { [$2] }
  | LPAREN pi_bind1 RPAREN pi_binds  { $2 :: $4 }

fun_abstraction:
  | fun_bind1  { [$1] }
  | fun_binds  { $1 }

fun_bind1: mark_position(plain_fun_bind1) { $1 }
plain_fun_bind1:
  | xs=nonempty_list(NAME)             { (xs, None) }
  | xs=nonempty_list(NAME) COLON term  { (xs, Some $3) }

fun_binds:
  | LPAREN fun_bind1 RPAREN            { [$2] }
  | LPAREN fun_bind1 RPAREN fun_binds  { $2 :: $4 }

mark_position(X):
  x = X
  { x, Common.Position ($startpos, $endpos) }

%%
