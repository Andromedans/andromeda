open Parser
open Ulexbuf

let reserved = [
  ("Axiom", PRIMITIVE) ;
  ("and", AND) ;
  ("beta", BETA) ;
  ("Beta", TOPBETA) ;
  ("Check", TOPCHECK) ;
  ("eta", ETA) ;
  ("Eta", TOPETA) ;
  ("hint", HINT) ;
  ("Hint", TOPHINT) ;
  ("unhint", UNHINT) ;
  ("Unhint", TOPUNHINT) ;
  ("Hypothesis", PRIMITIVE) ;
  ("inhabit", INHABIT) ;
  ("Inhabit", TOPINHABIT) ;
  ("Let", TOPLET) ;
  ("let", LET) ;
  ("Parameter", PRIMITIVE) ;
  ("reduce", REDUCE) ;
  ("forall", FORALL) ;
  ("∀", FORALL) ;
  ("Π", FORALL) ;
  ("fun", FUN) ;
  ("λ", FUN) ;
  ("in", IN) ;
  ("refl", REFL) ;
  ("Type", TYPE) ;
]

let ascii_name =
  [%sedlex.regexp? ('a'..'z' | 'A'..'Z') ,
                 Star ('_' | 'a'..'z' | 'A'..'Z' | '0'..'9' | '\'')]
let name =
  [%sedlex.regexp? (alphabetic | math),
                 Star ('_' | alphabetic | math
                      | 8304 .. 8351 (* sub-/super-scripts *)
                      | '0'..'9' | '\'')]

let digit = [%sedlex.regexp? '0'..'9']
let numeral = [%sedlex.regexp? Plus digit]

let project = [%sedlex.regexp? '.', (name | numeral)]

let start_longcomment = [%sedlex.regexp? "(*"]
let end_longcomment= [%sedlex.regexp? "*)"]

let newline = [%sedlex.regexp? ('\n' | '\r' | "\n\r" | "\r\n")]
let hspace  = [%sedlex.regexp? (' ' | '\t' | '\r')]

let quoted_string = [%sedlex.regexp? '"', Plus (Compl '"'), '"']

let update_eoi ({ pos_end; end_of_input; line_limit } as lexbuf) =
  match line_limit with None -> () | Some line_limit ->
    if pos_end.Lexing.pos_lnum >= line_limit
    then reached_end_of_input lexbuf

let rec token ({ end_of_input } as lexbuf) =
  if end_of_input then EOF else token_aux lexbuf

and token_aux ({ stream; pos_end; end_of_input; line_limit } as lexbuf) =
  let f () = update_pos lexbuf in
  (* [g] updates the lexbuffer state to indicate whether a sensible end of
     input has been found, typically after a dot or a directive *)
  let g () = update_eoi lexbuf in
  match%sedlex stream with
  | newline                  -> f (); new_line lexbuf; token_aux lexbuf
  | start_longcomment        -> f (); comments 0 lexbuf
  | Plus hspace              -> f (); token_aux lexbuf
  | "#context"               -> f (); g (); CONTEXT
  | "#help"                  -> f (); g (); HELP
  | "#quit"                  -> f (); g (); QUIT
  | "#verbosity", Plus hspace -> g (); verbosity lexbuf
  | "#include"               -> f (); INCLUDE
  | quoted_string            -> f (); QUOTED_STRING (lexeme lexbuf)
  | '('                      -> f (); LPAREN
  | ')'                      -> f (); RPAREN
  | '['                      -> f (); LBRACK
  | ']'                      -> f (); RBRACK
  | ':'                      -> f (); COLON
  | ":="                     -> f (); COLONEQ
  | ','                      -> f (); COMMA
  | '.'                      -> f (); g (); DOT
  | '_'                      -> f (); UNDERSCORE
  | "->" | 10230             -> f (); ARROW
  | "=>" | 10233             -> f (); DARROW
  | "==" | 8801              -> f (); EQEQ
  | eof                      -> f (); EOF
  | (name | numeral)         -> f ();
    let n = lexeme lexbuf in
    begin try List.assoc n reserved
    with Not_found -> NAME n
    end
  | any -> f ();
    let c = lexeme lexbuf in
    Error.syntax ~loc:(Location.of_lexeme lexbuf)
      "Unexpected character: %s" c
  | _ -> f ();
    Error.syntax ~loc:(Location.of_lexeme lexbuf)
      "Unexpected character, failed to parse"

and verbosity ({ stream } as lexbuf) =
  begin match%sedlex stream with
  | Opt '-', digit ->
    update_pos lexbuf;
    VERBOSITY (int_of_string (lexeme lexbuf))
  | _ ->
    Error.syntax ~loc:(Location.of_lexeme lexbuf) "Expected integer verbosity level"
  end

and comments level ({ stream } as lexbuf) =
  match%sedlex stream with
  | end_longcomment ->
    if level = 0 then
      begin update_pos lexbuf; token lexbuf end
    else
      comments (level-1) lexbuf

  | start_longcomment -> comments (level+1) lexbuf
  | '\n'        -> new_line lexbuf; comments level lexbuf
  | eof         ->
    print_endline "Input ended inside (unclosed) comment";
    raise End_of_file
  | any           -> comments level lexbuf
  | _ -> Error.syntax ~loc:(Location.of_lexeme lexbuf)
           "Unexpected character in comment"


(** run a menhir parser with a sedlexer on a t *)
(* the type of run is also:  *)
(* (t -> 'a) -> ('a, 'b) MenhirLib.Convert.traditional -> t -> 'b *)
let run
    ?(line_limit : int option)
    (lexer : t -> 'a)
    (parser : (Lexing.lexbuf -> 'a) -> Lexing.lexbuf -> 'b)
    (lexbuf : t) : 'b =
  set_line_limit line_limit lexbuf;
  let lexer () =
    let token = lexer lexbuf in
    (token, lexbuf.pos_start, lexbuf.pos_end) in
  let parser = MenhirLib.Convert.Simplified.traditional2revised parser in
  try
    parser lexer
  with
  | Parser.Error
  | Sedlexing.MalFormed
  | Sedlexing.InvalidCodepoint _ ->
    raise (Parse_Error lexbuf)


let read_file ?line_limit parse fn =
  try
    let fh = open_in fn in
    let lex = from_channel ~fn fh in
    try
      let terms = run ?line_limit token parse lex in
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
  let lex = from_string (str ^ "\n") in
  run token parse lex
