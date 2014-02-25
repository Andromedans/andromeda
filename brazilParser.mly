%{
  open BrazilInput

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

%token FORALL FUN
%token <string> NAME
%token <int> NUM
%token LPAREN RPAREN
%token COLON ASCRIBE COMMA SEMISEMI
%token ARROW DARROW STAR
%token <string> PROJ
%token <int> TYPE
%token <int> FIB
%token JEQUIV JEQUAL
%token REFLEQUIV REFLEQUAL
%token EQEQUIV EQEQUAL
%token COLONEQ
%token EQ EQEQ AT
(* %token EVAL *)
%token DEFINE
(*%token LET IN*)
%token ASSUME
%token HANDLE WITH BAR END
(*%token RETURN*)
%token QUIT HELP  CONTEXT
%token EOF


%start <Common.variable BrazilInput.toplevel list> file
%start <Common.variable BrazilInput.toplevel> commandline


%%

(* Toplevel syntax *)

(* If you're going to "optimize" this, please make sure we don't require;; at the
   end of the file. *)
file:
  | filecontents EOF            { $1 }

filecontents:
  |                              { [] }
  | topdef filecontents          { $1 :: $2 }
  | topdirective filecontents    { $1 :: $2 }
  | tophandler filecontents      { $1 :: $2 }

tophandler: mark_position(plain_tophandler) { $1 }
plain_tophandler:
  | WITH handler { TopHandler($2) }

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
  | plain_equiv_term                  { $1 }
  | FORALL pi_abstraction COMMA term  { fst (make_pi $4 $2) }
  | FUN fun_abstraction DARROW term   { fst (make_lambda $4 $2) }

equiv_term: mark_position(plain_equiv_term) { $1 }
plain_equiv_term:
    | plain_arrow_term                         { $1 }
    | arrow_term EQEQ arrow_term AT equiv_term { Equiv(Ju, $1, $3, $5) }
    | arrow_term EQ arrow_term AT equiv_term   { Equiv(Pr, $1, $3, $5) }

arrow_term: mark_position(plain_arrow_term) { $1 }
plain_arrow_term:
  | plain_app_term              { $1 }
  | app_term ARROW arrow_term   { Pi ("_", $1, $3) }
  | LPAREN NAME COLON term RPAREN ARROW arrow_term      { Pi($2, $4, $7) }
  | app_term STAR arrow_term    { Sigma ("_", $1, $3) }
  | LPAREN NAME COLON term RPAREN STAR arrow_term      { Sigma($2, $4, $7) }

app_term: mark_position(plain_app_term) { $1 }
plain_app_term:
  | plain_simple_term      { $1 }
  | app_term simple_term   { App ($1, $2) }
  | REFLEQUIV simple_term          { Refl(Ju, $2) }
  | REFLEQUAL simple_term          { Refl(Pr, $2) }
  | EQEQUAL simple_term simple_term simple_term { Equiv(Pr, $3, $4, $2) }
  | EQEQUIV simple_term simple_term simple_term { Equiv(Ju, $3, $4, $2) }

simple_term: mark_position(plain_simple_term) { $1 }
plain_simple_term:
  | NAME                            { Var $1 }
  | NUM                             { Num $1 }
  | FIB             { Universe (Fib $1) }
  | TYPE            { Universe (Type $1) }
  | LPAREN plain_term RPAREN        { $2 }
  | LPAREN term COMMA term RPAREN   { Pair($2, $4) }
  | LPAREN term ASCRIBE term RPAREN { Ascribe ($2, $4) }
  | HANDLE term WITH handler END    { Handle ($2, $4) }
  | JEQUIV LPAREN term COMMA term COMMA term RPAREN
                                    { J(Ju,$3,$5,$7) }
  | JEQUAL LPAREN term COMMA term COMMA term RPAREN
                                    { J(Pr,$3,$5,$7) }
  | simple_term PROJ                { Proj($2, $1) }

handler:
  | cs=separated_list(BAR, term)  { cs }


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
