
open Parser

let reserved = [
  ("_", UNDERSCORE) ;
  ("_atom", UATOM) ;
  ("abstract", ABSTRACT);
  ("and", AND) ;
  ("as", AS) ;
  ("boundary", MLBOUNDARY) ;
  ("by", BY) ;
  ("congruence", CONGRUENCE) ;
  ("context", CONTEXT) ;
  ("convert", CONVERT) ;
  ("derive", DERIVE) ;
  ("derivation", MLDERIVATION) ;
  ("end", END) ;
  ("exception", EXCEPTION) ;
  ("external", EXTERNAL) ;
  ("fresh", FRESH) ;
  ("fun", FUN) ;
  ("try", TRY) ;
  ("handler", HANDLER) ;
  ("in", IN) ;
  ("include", INCLUDE) ;
  ("judgement", MLJUDGEMENT) ;
  ("judgment", MLJUDGEMENT) ; (* for Egbert Rijke and other Americans *)
  ("let", LET) ;
  ("match", MATCH) ;
  ("meta", META) ;
  ("mlforall", MLFORALL) ;
  ("mlstring", MLSTRING) ;
  ("mltype", MLTYPE) ;
  ("mlunit", MLUNIT) ;
  ("module", MODULE) ;
  ("natural", NATURAL) ;
  ("occurs", OCCURS) ;
  ("of", OF) ;
  ("open", OPEN) ;
  ("operation", OPERATION) ;
  ("raise", RAISE) ;
  ("rewrite", REWRITE) ;
  ("rec", REC) ;
  ("ref", REF) ;
  ("rule", RULE) ;
  ("type", TYPE) ;
  ("require", REQUIRE) ;
  ("struct", STRUCT) ;
  ("val", VAL) ;
  ("verbosity", VERBOSITY) ;
  ("when", WHEN) ;
  ("with", WITH) ;
]

let name =
  [%sedlex.regexp? (('_' | alphabetic),
                    Star ('_' | alphabetic
                         | 185 | 178 | 179 | 8304 .. 8351 (* sub-/super-scripts *)
                         | '0'..'9' | '\'')) | math]

let qname =
  [%sedlex.regexp? '?', name]

let digit = [%sedlex.regexp? '0'..'9']
let numeral = [%sedlex.regexp? Plus digit]

let symbolchar = [%sedlex.regexp?  ('!' | '$' | '%' | '&' | '*' | '+' | '-' | '.' | '/' | ':' | '<' | '=' | '>' | '?' | '@' | '^' | '|' | '~' | 215 )]

let prefixop = [%sedlex.regexp? ('~' | '?' | '!'), Star symbolchar ]
let infixop0 = [%sedlex.regexp? ('=' | '<' | '>' | '|' | '&' | '$'), Star symbolchar]
let infixop1 = [%sedlex.regexp? ('@' | '^'), Star symbolchar ]
let infixcons = [%sedlex.regexp? "::"]
let infixop2 = [%sedlex.regexp? ('+' | '-'), Star symbolchar ]
let infixop3 = [%sedlex.regexp? ('*' | '/' | '%'| 215), Star symbolchar ]
let infixop4 = [%sedlex.regexp? "**", Star symbolchar ]

let start_longcomment = [%sedlex.regexp? "(*"]
let end_longcomment= [%sedlex.regexp? "*)"]

let newline = [%sedlex.regexp? ('\n' | '\r' | "\n\r" | "\r\n")]
let hspace  = [%sedlex.regexp? (' ' | '\t' | '\r')]

let quoted_string = [%sedlex.regexp? '"', Star (Compl '"'), '"']

let update_eoi ({ Ulexbuf.pos_end; line_limit;_ } as lexbuf) =
  match line_limit with None -> () | Some line_limit ->
    if pos_end.Lexing.pos_lnum >= line_limit
    then Ulexbuf.reached_end_of_input lexbuf

let at_of lex = Location.make lex.Ulexbuf.pos_start lex.Ulexbuf.pos_end

let safe_int_of_string lexbuf =
  let s = Ulexbuf.lexeme lexbuf in
  try int_of_string s
  with Failure _ -> Ulexbuf.error ~at:(at_of lexbuf) (Ulexbuf.BadNumeral s)

let rec token ({ Ulexbuf.end_of_input;_ } as lexbuf) =
  if end_of_input then EOF else token_aux lexbuf

and token_aux ({ Ulexbuf.stream;_ } as lexbuf) =
  let f () = Ulexbuf.update_pos lexbuf in
  match%sedlex stream with
  | newline                  -> f (); Ulexbuf.new_line lexbuf; token_aux lexbuf
  | start_longcomment        -> f (); comments 0 lexbuf
  | Plus hspace              -> f (); token_aux lexbuf
  | quoted_string            -> f ();
     let s = Ulexbuf.lexeme lexbuf in
     let l = String.length s in
     let n = ref 0 in
     String.iter (fun c -> if c = '\n' then incr n) s;
     Ulexbuf.new_line ~n:!n lexbuf;
     QUOTED_STRING (String.sub s 1 (l - 2))
  | '('                      -> f (); LPAREN
  | ')'                      -> f (); RPAREN
  | '['                      -> f (); LBRACK
  | ']'                      -> f (); RBRACK
  | '{'                      -> f (); LBRACE
  | '}'                      -> f (); RBRACE
  | ':'                      -> f (); COLON
  | ":?"                     -> f (); COLONQT
  | ":>"                     -> f (); COLONGT
  | ','                      -> f (); COMMA
  | '.'                      -> f (); PERIOD
  | '|'                      -> f (); BAR
  | "->" | 8594 | 10230      -> f (); ARROW
  | "=>" | 8658 | 10233      -> f (); DARROW
  | "==" | 8801              -> f (); EQEQ
  | '!'                      -> f (); BANG
  | ":="                     -> f (); COLONEQ
  | ";;"                     -> f (); SEMISEMI
  | ';'                      -> f (); SEMI
  (* We record the location of operators here because menhir cannot handle %infix and
     mark_location simultaneously, it seems. *)
  | "??" | 8263 (* ⁇ *)      -> f (); QQMARK (Name.mk_name ~fixity:Name.Prefix (Ulexbuf.lexeme lexbuf), at_of lexbuf)
  | prefixop                 -> f (); PREFIXOP (let s = Ulexbuf.lexeme lexbuf in
                                                Name.mk_name ~fixity:Name.Prefix s, at_of lexbuf)
  (* Comes before infixop0 because it also matches infixop0. *)
  | '='                      -> f (); EQ (Name.mk_name ~fixity:(Name.Infix Level.Infix0) "=", at_of lexbuf)
  | infixop0                 -> f (); INFIXOP0 (let s = Ulexbuf.lexeme lexbuf in
                                                Name.mk_name ~fixity:(Name.Infix Level.Infix0) s, at_of lexbuf)
  | infixop1                 -> f (); INFIXOP1 (let s = Ulexbuf.lexeme lexbuf in
                                                Name.mk_name ~fixity:(Name.Infix Level.Infix1) s, at_of lexbuf)
  | infixcons                -> f (); INFIXCONS(let s = Ulexbuf.lexeme lexbuf in
                                                Name.mk_name ~fixity:(Name.Infix Level.InfixCons) s, at_of lexbuf)
  | infixop2                 -> f (); INFIXOP2 (let s = Ulexbuf.lexeme lexbuf in
                                                Name.mk_name ~fixity:(Name.Infix Level.Infix2) s, at_of lexbuf)
  (* Comes before infixop3 because ** matches the infixop3 pattern too *)
  | infixop4                 -> f (); INFIXOP4 (let s = Ulexbuf.lexeme lexbuf in
                                                Name.mk_name ~fixity:(Name.Infix Level.Infix4) s, at_of lexbuf)
  (* Comes before infixop3 because * matches the infixop3 pattern too *)
  | '*'                      -> f (); STAR (Name.mk_name ~fixity:(Name.Infix Level.Infix3) "*", at_of lexbuf)
  | infixop3                 -> f (); INFIXOP3 (let s = Ulexbuf.lexeme lexbuf in
                                                Name.mk_name ~fixity:(Name.Infix Level.Infix3) s, at_of lexbuf)

  | qname                    -> f (); QNAME (let s = Ulexbuf.lexeme lexbuf in Name.mk_name (String.sub s 1 (String.length s - 1)))

  | name                     -> f ();
     let n = Ulexbuf.lexeme lexbuf in
     begin try List.assoc n reserved
     with Not_found -> NAME (Name.mk_name n)
     end

  | numeral                  -> f (); let k = safe_int_of_string lexbuf in NUMERAL k

  | any -> f ();
     let w = Ulexbuf.lexeme lexbuf in
     let at = at_of lexbuf in
     Ulexbuf.error ~at (Ulexbuf.Unexpected w)

  | eof                      -> f (); EOF

  | _ -> assert false

and comments level ({ Ulexbuf.stream;_ } as lexbuf) =
  match%sedlex stream with
  | end_longcomment ->
     if level = 0 then
       begin Ulexbuf.update_pos lexbuf; token lexbuf end
     else
       comments (level-1) lexbuf

  | start_longcomment -> comments (level+1) lexbuf
  | '\n'        -> Ulexbuf.new_line lexbuf; comments level lexbuf
  | eof         -> Ulexbuf.error ~at:(at_of lexbuf) Ulexbuf.UnclosedComment
  | any         -> comments level lexbuf
  | _           -> assert false


(** run a menhir parser with a sedlexer on a t *)
(* the type of run is also:  *)
(* (t -> 'a) -> ('a, 'b) MenhirLib.Convert.traditional -> t -> 'b *)
let run
    ?(line_limit : int option)
    (lexer : Ulexbuf.t -> 'a)
    (parser : (Lexing.lexbuf -> 'a) -> Lexing.lexbuf -> 'b)
    (lexbuf : Ulexbuf.t) : 'b =
  Ulexbuf.set_line_limit line_limit lexbuf;
  let lexer () =
    let token = lexer lexbuf in
    (token, lexbuf.Ulexbuf.pos_start, lexbuf.Ulexbuf.pos_end) in
  let parser = MenhirLib.Convert.Simplified.traditional2revised parser in
  try
    parser lexer
  with
  | Parser.Error ->
     let w = Ulexbuf.lexeme lexbuf in
     let at = at_of lexbuf in
     Ulexbuf.error ~at (Ulexbuf.Unexpected w)
  | Sedlexing.MalFormed ->
     let at = at_of lexbuf in
     Ulexbuf.error ~at Ulexbuf.MalformedUTF8
  | Invalid_argument s
       (* work around https://github.com/ocaml-community/sedlex/issues/91 *)
       when
         let ulex_err = "is not an Unicode scalar value" in
         try let suffix = String.(sub s (length s - (length ulex_err)) (length ulex_err)) in
             ulex_err = suffix
         with Invalid_argument _ -> false
       -> let at = at_of lexbuf in
          Ulexbuf.error ~at Ulexbuf.MalformedUTF8
  (* | Sedlexing.InvalidCodepoint _ -> *)
  (*    assert false (\* Shouldn't happen with UTF8 *\) *)


let read_file ?line_limit parse fn =
  try
    let fh = open_in fn in
    let lex = Ulexbuf.from_channel ~fn fh in
    try
      let terms = run ?line_limit token parse lex in
      close_in fh;
      terms
    with
    (* Close the file in case of any parsing errors. *)
      Ulexbuf.Error err -> close_in fh; raise (Ulexbuf.Error err)
  with
  (* Any errors when opening or closing a file are fatal. *)
    Sys_error msg -> raise (Ulexbuf.error ~at:Location.unknown (Ulexbuf.SysError msg))


let read_toplevel parse () =
  let all_white str =
    let n = String.length str in
    let rec fold k =
      k >= n ||
      (str.[k] = ' ' || str.[k] = '\n' || str.[k] = '\t') && fold (k+1)
    in
    fold 0
  in

  let ends_with_backslash_or_empty str =
    let i = String.length str - 1 in
    if i >= 0 && str.[i] = '\\'
    then (true, String.sub str 0 i)
    else (all_white str, str)
  in

  let rec read_more prompt acc =
    print_string prompt ;
    let str = read_line () in
    let more, str = ends_with_backslash_or_empty str in
    let acc = acc ^ "\n" ^ str in
    if more
    then read_more "  " acc
    else acc
  in

  let str = read_more "# " "" in
  let lex = Ulexbuf.from_string (str ^ "\n") in
  run token parse lex

let read_string parse s =
  let lex = Ulexbuf.from_string s in
  run token parse lex
