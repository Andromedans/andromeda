(** Definitions in common use *)

(** Variable names *)
type variable = string

(** Position in source code. For each type in the abstract syntax we define two versions
    [t] and [t']. The former is the latter with a position tag. For example, [expr = expr'
    * position] and [expr'] is the type of expressions (without positions).
*)
type position =
  | Position of Lexing.position * Lexing.position (** delimited position *)
  | Nowhere (** unknown position *)

(** [nowhere e] is the expression [e] without a source position. It is used when
    an expression is generated and there is not reasonable position that could be
    assigned to it. *)
let nowhere x = (x, Nowhere)

let string_of_position ?(full=false) = function
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
