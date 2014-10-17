(** Position in source code. For each type in the input syntax we define two versions
    [t] and [t']. The former is the latter with a position tag. For example, [term = term'
    * position] and [term'] is the type of terms without positions. *)
type t =
  | Position of Lexing.position * Lexing.position (** delimited position *)
  | Nowhere (** unknown position *)

let nowhere = Nowhere

let make start_post end_pos = Position (start_post, end_pos)

let of_lex lex =
  Position (Lexing.lexeme_start_p lex, Lexing.lexeme_end_p lex)

let to_string ?(full=false) = function
  | Nowhere -> "?:?"
  | Position (p1,p2) when full ->
      let filename = p1.Lexing.pos_fname  in
      let line1 = p1.Lexing.pos_lnum in
      let line2 = p2.Lexing.pos_lnum in
      let col1  = p1.Lexing.pos_cnum - p1.Lexing.pos_bol + 1  in
      let col2  = p2.Lexing.pos_cnum - p2.Lexing.pos_bol + 1 in
      if (line1 = line2) then
        Printf.sprintf "%s:%d:%d-%d" filename line1 col1 col2
      else
        Printf.sprintf "%s:%d:%d-%d:%d" filename line1 col1 line2 col2
  | Position (p1,p2) ->
      let filename = p1.Lexing.pos_fname  in
      let line1 = p1.Lexing.pos_lnum in
      let col1  = p1.Lexing.pos_cnum - p1.Lexing.pos_bol + 1  in
      Printf.sprintf "%s:%d:%d" filename line1 col1

let get_range = function
  | Nowhere -> Lexing.dummy_pos, Lexing.dummy_pos
  | Position(startp, endp) -> startp, endp
