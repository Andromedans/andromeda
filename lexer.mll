{
  open Parser

  let reserved = [
    ("forall", FORALL);
    ("fun", FUN);
    ("Type", TYPE);
  ]
}

let name = ['a'-'z' 'A'-'Z'] ['_' 'a'-'z' 'A'-'Z' '0'-'9' '\'']*

let numeral = ['0'-'9']+

rule token = parse
  | '\n'                { Lexing.new_line lexbuf; token lexbuf }
  | [' ' '\r' '\t']     { token lexbuf }
  | numeral             { NUMERAL (int_of_string (Lexing.lexeme lexbuf)) }
  | name                { let s = Lexing.lexeme lexbuf in
                          try List.assoc s reserved with Not_found -> NAME s
                        }
  | '('                 { LPAREN }
  | ')'                 { RPAREN }
  | "#quit"             { QUIT }
  | "#help"             { HELP }
  | "#assume"           { ASSUME }
  | "#context"          { CONTEXT }
  | ";;"                { SEMISEMI }
  | ':'                 { COLON }
  | ','                 { COMMA }
  | "->"                { ARROW }
  | "=>"                { DARROW }
  | eof                 { EOF }


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
    Sys_error msg -> Error.fatal "%s" msg


  let read_toplevel parser () =

    let has_semisemi str =
      let last_semi = ref false in
      let semisemi = ref false in
      let i = ref 0 in
      while !i < String.length str && not !semisemi do
        begin
          match str.[!i], !last_semi with
            | ';', b -> semisemi := b; last_semi := true
            | _, _ -> last_semi := false
        end;
        incr i
      done;
      if !semisemi then
        Some (String.sub str 0 !i)
      else
        None
    in

    let rec read_more prompt acc =
      match has_semisemi acc with
      | Some acc -> acc
      | None ->
          print_string prompt;
          let str = read_line () in
          read_more "  " (acc ^ "\n" ^ str)
    in

    let str = read_more "# " "" in
    let lex = Lexing.from_string (str ^ "\n") in
      parser lex
}

