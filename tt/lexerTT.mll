{
  (** The lexer. *)

  open ParserTT

  let reserved = [
    ("assume", ASSUME) ;
    ("debruijn", DEBRUIJN);
    ("define", DEFINE) ;
    ("end", END);
    ("fun", FUN);
    ("handle", HANDLE) ;
    ("handler", HANDLER) ;
    ("lambda", LAMBDA) ;
    ("let", LET) ;
    ("in", IN) ;
    ("match", MATCH);
    ("with", WITH) ;
    ("op", OP);
  ]

}

let name = ['a'-'z' 'A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']*
let patternvar = '?' name

let numeral = ['0'-'9']+

let start_longcomment = "/*"
let end_longcomment = "*/"

rule token = parse
  | start_longcomment { comments 0 lexbuf }

  | '\n'                { Lexing.new_line lexbuf; token lexbuf }
  | "//"[^'\n']*        { token lexbuf }
  | [' ' '\r' '\t']     { token lexbuf }
  | "#context"          { CONTEXT }
  (*| "#eval"             { EVAL }*)
  | "#help"             { HELP }
  | "#quit"             { QUIT }

  | ":>"                { ASCRIBE }
  | '|'                 { BAR }
  | ':'                 { COLON }
  | ":="                { COLONEQ }
  | ','                 { COMMA }
  | "=>"                { DARROW }
  | eof                 { EOF }
  | "="                 { EQ }
  | '['                 { LBRACK }
  | '('                 { LPAREN }
  | ']'                 { RBRACK }
  | ')'                 { RPAREN }


  | numeral as s        { INT (int_of_string s) }
  | "true"              { BOOL true }
  | "false"             { BOOL false }
  | "()"                { UNIT }

  | "inj" [' ' '\t']* (numeral as s) { INJ (int_of_string s) }

  | name
                       { let s = Lexing.lexeme lexbuf in
                            try
                              List.assoc s reserved
                            with Not_found -> NAME s
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
  let read_file parser fn =
  try
    let fh = open_in fn in
    let lex = Lexing.from_channel fh in
    lex.Lexing.lex_curr_p <- {lex.Lexing.lex_curr_p with Lexing.pos_fname = fn};
    try
      let terms = parser lex in
      close_in fh;
      terms
    with
      (* Close the file in case of any parsing errors. *)
      Error.Error err -> close_in fh; raise (Error.Error err)
  with
    (* Any errors when opening or closing a file are fatal. *)
    Sys_error msg -> Error.fatal ~loc:Position.nowhere "%s" msg


  let read_toplevel parser () =
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
      parser lex
}

