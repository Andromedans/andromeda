type t = {
  stream : Sedlexing.lexbuf ;
  mutable pos_start : Lexing.position ;
  mutable pos_end : Lexing.position ;
  mutable line_limit : int option ;
  mutable end_of_input : bool ;
}

exception Parse_Error of string * Lexing.position * Lexing.position

let create_lexbuf ?(fn="?") stream =
  let pos_end =
    Lexing.{
      pos_fname = fn;
      pos_lnum = 1;
      pos_bol = 0;
      pos_cnum = 0;
    }
  in
  { pos_start = pos_end; pos_end; stream ;
    line_limit = None; end_of_input = false; }

let from_channel ?(fn="?") fh =
  create_lexbuf ~fn (Sedlexing.Utf8.from_channel fh)

let from_string ?(fn="?") s =
  create_lexbuf ~fn (Sedlexing.Utf8.from_string s)

let lexeme { stream;_ } = Sedlexing.Utf8.lexeme stream

let new_line ?(n=1) lexbuf =
  assert (n >= 0) ;
  if n = 0 then () else
    let open Lexing in
    let lcp = lexbuf.pos_end in
    lexbuf.pos_end <-
      { lcp with
        pos_lnum = lcp.pos_lnum + n ;
        pos_bol = lcp.pos_cnum ;
      }

let update_pos ({pos_end; pos_start; stream;_} as buf) =
  let p_start, p_end = Sedlexing.loc stream in
  buf.pos_start <- {pos_end with Lexing.pos_cnum = p_start};
  buf.pos_end <- {pos_end with Lexing.pos_cnum = p_end }

let reached_end_of_input b =
  b.end_of_input <- true

let set_line_limit ll b =
  b.line_limit <- ll

let parse lex parse resource =
  try
    lex parse resource
  with
  | Parse_Error (w, p_start, p_end) ->
     let loc = Location.make p_start p_end in
     Error.syntax ~loc "Unexpected: %s" w

