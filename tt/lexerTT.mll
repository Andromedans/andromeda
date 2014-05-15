{
  (** The lexer. *)

  open ParserTT

  let reserved = [
    ("assume", ASSUME) ;
    ("debruijn", DEBRUIJN);
    ("define", DEFINE) ;
    ("end", END);
    ("eval", EVAL);
    ("finally", FINALLY);
    ("forall", FORALL);
    ("fun", FUN);
    ("handle", HANDLE) ;
    ("handler", HANDLER) ;
    ("in", IN) ;
    ("lambda", LAMBDA) ;
    ("let", LET) ;
    ("match", MATCH);
    ("op", OP);
    ("val", VAL);
    ("when", WHEN) ;
    ("whnf", WHNF) ;
    ("with", WITH) ;
  ]

(* Code for recording where newlines are found in the input, so that
   we can use the built-in support for converting error locations
   (character-in-the-file) into a more human-readable line/column
   format.⎵

   This function was adapted from the example code at
   http://plus.kaist.ac.kr/~shoh/ocaml/ocamllex-ocamlyacc/ocamlyacc-tutorial/sec-tracking-locations.html
*)
let incr_linenums n lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + n;
      Lexing.pos_bol =  pos.Lexing.pos_cnum;
    }

let incr_linenum = incr_linenums 1

let incr_linenum_string str lexbuf =
  let f = function
    | '\n' -> incr_linenum lexbuf
    | _ -> ()
  in
    String.iter f str

}

let name = ['a'-'z' 'A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']*
let patternvar = '?' name

let numeral = ['0'-'9']+

let start_longcomment = "/*"
let end_longcomment = "*/"

let brazil_term_code = '`' [^ '`']* '`'
let brazil_type_code = "t`" [^ '`']* '`'

rule token = parse
  | start_longcomment { comments 0 lexbuf }

  | '\n'                { incr_linenum lexbuf; token lexbuf }
  | "//"[^'\n']*        { token lexbuf }
  | [' ' '\r' '\t']     { token lexbuf }
  | "#context"          { CONTEXT }
  (*| "#eval"             { EVAL }*)
  | "#help"             { HELP }
  | "#quit"             { QUIT }

  | "&&"                { ANDAND }
  | ":>"                { ASCRIBE }
  | '!'                 { BANG }
  | '|'                 { BAR }
  | ':'                 { COLON }
  | ":="                { COLONEQ }
  | ','                 { COMMA }
  | "=>"                { DARROW }
  | '-'                 { DASH }
  | eof                 { EOF }
  | "="                 { EQ }
  | "=="                { EQEQ }
  | '['                 { LBRACK }
  | '('                 { LPAREN }
  | "<>"                { LTGT }
  | "+"                 { PLUS }
  | "++"                { PLUSPLUS }
  | ']'                 { RBRACK }
  | ')'                 { RPAREN }
  | ";;"                { SEMISEMI }
  | "*"                 { STAR }
  | "_"                 { UNDERSCORE }


  | numeral as s        { INT (int_of_string s) }
  | "true"              { BOOL true }
  | "false"             { BOOL false }
  | "()"                { UNIT }
  | '"' ([^ '"' '\n']* as s) '"' { STRING s }

  | "inj" [' ' '\t']* (numeral as s) { INJ (int_of_string s) }

  | name
                       { let s = Lexing.lexeme lexbuf in
                            try
                              List.assoc s reserved
                            with Not_found -> NAME s
                        }

  | brazil_term_code as s   { (* Strip quotes *)
                              let code = String.sub s 1 (String.length s - 2) in
                              incr_linenum_string s lexbuf;
                              BRAZILTERM code }

  | brazil_type_code as s   { (* Strip quotes *)
                              let code = String.sub s 2 (String.length s - 3) in
                              incr_linenum_string s lexbuf;
                              BRAZILTYPE code
                            }

  | _ as c              { Error.syntax
                          ~loc:(Position.make (Lexing.lexeme_start_p lexbuf) (Lexing.lexeme_end_p lexbuf))
                          "Unexpected character %s" (Char.escaped c)
                        }

(* Code to skip over nested comments
*)
and comments level = parse
  | end_longcomment     { if level = 0 then token lexbuf
                          else comments (level-1) lexbuf
                        }
  | start_longcomment   { comments (level+1) lexbuf }
  | '\n'        { Lexing.new_line lexbuf; comments level lexbuf }
  | _           { comments level lexbuf }
  | eof         { print_endline "Input ended inside (unclosed) comment";
                  raise End_of_file
                }


{
  let read_file parse fn =
  try
    let fh = open_in fn in
    let lex = Lexing.from_channel fh in
    lex.Lexing.lex_curr_p <- {lex.Lexing.lex_curr_p with Lexing.pos_fname = fn};
    try
      let terms = parse lex in
      close_in fh;
      terms
    with
      (* Close the file in case of any parsing errors. *)
      Error.Error err -> close_in fh; raise (Error.Error err)
  with
    (* Any errors when opening or closing a file are fatal. *)
    Sys_error msg -> Error.fatal ~loc:Position.nowhere "%s" msg


  let read_toplevel parse () =
    let ends_with_backslash str =
      let i = String.length str - 1 in
        if i >= 0 && str.[i] = '\\'
        then (true, String.sub str 0 i)
        else (false, str)
    in

    let rec read_more prompt acc =
      print_string prompt ;
      let str = read_line () in
      let more, str = ends_with_backslash str in
      let acc = acc ^ "\n" ^ str in
        if more
        then read_more "  " acc
        else acc
    in

    let str = read_more "# " "" in
    let lex = Lexing.from_string (str ^ "\n") in
      parse lex
}

