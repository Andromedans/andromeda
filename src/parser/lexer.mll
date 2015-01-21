{
  (** The lexer. *)

  open Parser

  let reserved = [
    ("and", AND) ;
    ("Check", TOPCHECK) ;
    ("Let", TOPLET) ;
    ("let", LET) ;
    ("Parameter", PARAMETER) ;
    ("forall", FORALL) ;
    ("fun", FUN) ;
    ("in", IN) ;
    ("refl", REFL) ;
    ("Type", TYPE) ;
  ]

}

let name = ['a'-'z' 'A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']*

let numeral = ['0'-'9']+

let project = '.' (name | numeral)

let start_longcomment = "(*"
let end_longcomment = "*)"

rule token = parse
  | start_longcomment { comments 0 lexbuf }

  | '\n'                { Lexing.new_line lexbuf; token lexbuf }
  | [' ' '\r' '\t']     { token lexbuf }
  | "#context"          { CONTEXT }
  | "#help"             { HELP }
  | "#quit"             { QUIT }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | ':'                 { COLON }
  | ":="                { COLONEQ }
  | "::"                { ASCRIBE }
  | ','                 { COMMA }
  | '.'                 { DOT }
  | '_'                 { UNDERSCORE }
  | "->"                { ARROW }
  | "=>"                { DARROW }
  | "=="                { EQEQ }
  | eof                 { EOF }

  | (name | numeral)
                        { let s = Lexing.lexeme lexbuf in
                            try
                              List.assoc s reserved
                            with Not_found -> NAME s
                        }

  | _ as c              { Error.syntax
                          ~loc:(Location.of_lexeme lexbuf)
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
    Sys_error msg -> Error.fatal ~loc:Location.unknown "%s" msg


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
