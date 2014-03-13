{
  (** The lexer. *)

  open Parser

  let reserved = [
    ("assume", ASSUME) ;
    ("define", DEFINE) ;
    ("end", END) ;
    ("exists", EXISTS) ;
    ("forall", FORALL) ;
    ("fun", FUN);
    ("handle", HANDLE) ;
    (*("let", LET) ;*)
    (*("in", IN) ;*)
    (*("return", RETURN) ;*)
    ("refl", REFLEQUIV) ;
    ("idpath", REFLEQUAL) ;
    ("with", WITH) ;
    ("Ind", IND);
  ]

  let position_of_lex lex =
    Common.Position (Lexing.lexeme_start_p lex, Lexing.lexeme_end_p lex)
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
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | '['                 { LBRACK }
  | ']'                 { RBRACK }
  | ':'                 { COLON }
  | "::"                { DCOLON }
  | ":>"                { ASCRIBE }
  | "*"                 { STAR }
  | ";;"                { SEMISEMI }
  | ','                 { COMMA }
  | '.'                 { DOT }
  | '|'                 { BAR }
  | '?'                 { QUESTIONMARK }
  | "->"                { ARROW }
  | "=>"                { DARROW }
  | ":="                { COLONEQ }
  | "="                 { EQ }
  | "=="                { EQEQ }
  | "@"                 { AT }
  | ">->"               { COERCE }

  | "Type" [' ' '\t']* (numeral as s) { TYPE (int_of_string s) }
  | "Type"                            { TYPE 0 }

  | "QuasiType" [' ' '\t']* (numeral as s) { QUASITYPE (int_of_string s) }
  | "QuasiType"                            { QUASITYPE 0 }


  | eof                 { EOF }

  | (name | patternvar | numeral) 
                       { let s = Lexing.lexeme lexbuf in
                            try
                              List.assoc s reserved
                            with Not_found -> NAME s
                        }

  | _ as c              { Error.syntax ~loc:(position_of_lex lexbuf)
                             "Unexpected character %s" (Char.escaped c) }

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
    Sys_error msg -> Error.fatal ~loc:Common.Nowhere "%s" msg


  let read_toplevel parser () =
    let ends_with_semisemi str =
      let i = ref (String.length str - 1) in
        while !i >= 0 && List.mem str.[!i] [' '; '\n'; '\t'; '\r'] do decr i done ;
        !i >= 1 && str.[!i - 1] = ';' && str.[!i] = ';'
    in

    let rec read_more prompt acc =
      if ends_with_semisemi acc
      then acc
      else begin
        print_string prompt ;
        let str = read_line () in
          read_more "  " (acc ^ "\n" ^ str)
      end
    in

    let str = read_more "# " "" in
    let lex = Lexing.from_string (str ^ "\n") in
      parser lex
}
