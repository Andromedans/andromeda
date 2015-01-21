(** Location in source code. For each type in the input syntax we define two versions
    [t] and [t']. The former is the latter with a location tag. For example, [term = term'
    * location] and [term'] is the type of terms without locations. *)
type t =
  | Location of Lexing.position * Lexing.position (** delimited location *)
  | Nowhere (** unknown location *)

let nowhere = Nowhere

let make start_pos end_pos = Location (start_pos, end_pos)

let of_lex lex =
  Location (Lexing.lexeme_start_p lex, Lexing.lexeme_end_p lex)

let print ?(full=false) loc ppf =
  match loc with
  | Nowhere -> Print.print ppf "?:?"
  | Location (p1,p2) when full ->
      let filename = p1.Lexing.pos_fname  in
      let line1 = p1.Lexing.pos_lnum in
      let line2 = p2.Lexing.pos_lnum in
      let col1  = p1.Lexing.pos_cnum - p1.Lexing.pos_bol + 1  in
      let col2  = p2.Lexing.pos_cnum - p2.Lexing.pos_bol + 1 in
      if (line1 = line2) then
        Print.print ppf "%s:%d:%d-%d" filename line1 col1 col2
      else
        Print.print ppf "%s:%d:%d-%d:%d" filename line1 col1 line2 col2
  | Location (p1,p2) ->
      let filename = p1.Lexing.pos_fname  in
      let line1 = p1.Lexing.pos_lnum in
      let col1  = p1.Lexing.pos_cnum - p1.Lexing.pos_bol + 1  in
      Print.print ppf "%s:%d:%d" filename line1 col1

let get_range = function
  | Nowhere -> Lexing.dummy_pos, Lexing.dummy_pos
  | Location(startp, endp) -> startp, endp
