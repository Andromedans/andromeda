%{
  open InputTT

%}


%token <bool> BOOL
%token <string> BRAZILTERM
%token <string> BRAZILTYPE
%token <int> INJ
%token <int> INT
%token <string> NAME

%token ANDAND
%token ASCRIBE
%token ASSUME
%token BANG
%token BAR
%token COLON
%token COLONEQ
%token COMMA
%token CONTEXT
%token DARROW
%token DEBRUIJN
%token DEFAULT
%token DEFINE
%token END
%token EOF
%token EVAL
%token EQ
%token FINALLY
%token FUN
%token HANDLE
%token HANDLER
%token HELP
%token IN
%token LAMBDA
%token LBRACK
%token LET
%token LPAREN
%token MATCH
%token OP
%token PLUS
%token PLUSPLUS
%token QUIT
%token RBRACK
%token RPAREN
%token SEMISEMI
%token UNDERSCORE
%token UNIT
%token VAL
%token WITH


%start <InputTT.toplevel list> file
%start <InputTT.toplevel> commandline

%type <InputTT.handler> hcases
%type <InputTT.handler> handler

(*%nonassoc ASCRIBE*)
(*%right PLUSPLUS*)
(*%left PLUS ANDAND*)

%%

(* Toplevel syntax *)

file:
  | filecontents EOF            { $1 }

filecontents:
  |                                { [] }
  | topdef sso filecontents        { $1 :: $3 }
  | topdirective sso filecontents  { $1 :: $3 }
  (*| tophandler sso filecontents    { $1 :: $3 }*)

(*tophandler: mark_position(plain_tophandler) { $1 }*)
(*plain_tophandler:*)
  (*| WITH handler { TopHandler($2) }*)

commandline:
  | topdef SEMISEMI        { $1 }
  | topdirective SEMISEMI  { $1 }

(* Things that can be defined on toplevel. *)
topdef: mark_position(plain_topdef) { $1 }
plain_topdef:
  | LET NAME COLONEQ comp                  { TopLet ($2, $4) }
  | DEFINE ttname COLONEQ comp               { TopDef ($2, $4) }
  | EVAL comp                              { TopEval $2 }
  | ASSUME nonempty_list(ttname) COLON comp  { TopParam ($2, $4) }

(* Toplevel directive. *)
topdirective: mark_position(plain_topdirective) { $1 }
plain_topdirective:
  | CONTEXT    { Context }
  | HELP       { Help }
  | QUIT       { Quit }

sso :
  |          {}
  | SEMISEMI {}

(* Main syntax tree *)

exp: mark_position(plain_exp) { $1 }
plain_exp:
    | NAME                              { Var $1 }
    | handler                { Handler $1 }
    | LBRACK es=separated_list(COMMA, exp) RBRACK    { Tuple es }
    | const                  { Const $1 }
    | INJ exp               { Inj ($1, $2) }
    | LPAREN plain_exp RPAREN      { $2 }
    | FUN name DARROW comp    { Fun ($2, $4) }
    | DEFAULT { DefaultHandler }

comp: mark_position(plain_comp) { $1 }
plain_comp:
    | VAL exp        { Val $2 }
    | exp exp        { App ($1, $2) }
    | exp ASCRIBE exp        { Ascribe ($1, $3) }
    | LET name EQ comp IN comp { Let($2, $4, $6) }
    | OP NAME exp    { Op ($2, $3) }
    | WITH exp HANDLE comp  { WithHandle ($2, $4) }
    | HANDLE comp WITH exp  { WithHandle ($4, $2) }
    | MATCH e=exp WITH option(BAR) lst=separated_list(BAR, arm) END { Match (e, lst) }
    | DEBRUIJN INT       { MkVar $2 }
    | LAMBDA name COLON exp COMMA comp { MkLam($2, $4, $6) }
    | exp PLUS exp { Prim(Plus, [$1; $3]) }
    | exp PLUSPLUS exp { Prim(Append, [$1; $3]) }
    | exp ANDAND exp   { Prim(And, [$1; $3]) }
    | BANG exp         { Prim(Not, [$2]) }
    | LPAREN plain_comp RPAREN { $2 }
    | BRAZILTERM       { BrazilTermCode $1 }
    | BRAZILTYPE       { BrazilTypeCode $1 }

arm:
  pat DARROW comp { ($1, $3) }

pat:
    | LBRACK xs=separated_list(COMMA, NAME) RBRACK { PTuple xs }
    | INJ NAME  { PInj($1, $2) }
    | NAME      { PVar $1 }
    | const     { PConst $1 }
    | UNDERSCORE { PWild }

handler:
    | HANDLER hcs=hcases END { hcs }

    (*| HANDLER VAL x=NAME DARROW c=comp hcs=list(preceded(BAR, hcase)) END*)
                   (*{ { valH = (x,c); opH = hcs } }*)


hcases:
    |              { { valH = None; opH = []; finH = None; } }
    | option(BAR) OP op=NAME p=pat k=NAME DARROW c=comp hcs=hcases { { hcs with opH = (op,p,k,c)::hcs.opH }  }
    | option(BAR) VAL     xv=NAME DARROW cv=comp hcs=hcases { { hcs with
    valH=Some (xv,cv) } }
    | option(BAR) FINALLY xf=NAME DARROW cf=comp hcs=hcases { { hcs with finH=Some (xf,cf) } }

const:
    | INT  { Int $1 }
    | BOOL { Bool $1 }
    | UNIT { Unit }

name:
    | NAME       { $1 }
    | UNDERSCORE { "_" }

ttname:
    | NAME { $1 }
    | INT  { string_of_int $1 }

mark_position(X):
  x = X
  { x, Position.make $startpos $endpos }

%%
