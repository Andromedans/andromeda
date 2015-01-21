(** A location of a piece of syntax in a file or interactive input. 
    A location describes a range in the source, i.e., it has a starting
    and ending position (see [get_range]). *)
type t

(** Unknown location. *)
val nowhere : t

(** Make a location from a start and end position of the lexer *)
val make : Lexing.position -> Lexing.position -> t

(** Convert the current position in a lexing buffer to a location. *)
val of_lex : Lexing.lexbuf -> t

(** Convert a location to a readable string. *)
val print : ?full:bool -> t -> Format.formatter -> unit

(* Give the starting and ending position of a location *)
val get_range : t -> Lexing.position * Lexing.position
