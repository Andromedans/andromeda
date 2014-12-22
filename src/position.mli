type t

val nowhere : t
val make : Lexing.position -> Lexing.position -> t

val of_lex : Lexing.lexbuf -> t

val to_string : ?full:bool -> t -> string

val get_range : t -> Lexing.position * Lexing.position
