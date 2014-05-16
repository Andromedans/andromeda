
(** The type of file positions *)
type t

(** Unknown position *)
val nowhere : t

(** Make a position out of begining and ending position. *)
val make : Lexing.position -> Lexing.position -> t

(** Convert a position reported by lexer to position. *)
val of_lex : Lexing.lexbuf -> t

(** Convert position to a string. *)
val to_string : ?full:bool -> t -> string

(** Convert back to a pair of lexer positions *)
val get_range : t -> Lexing.position * Lexing.position

