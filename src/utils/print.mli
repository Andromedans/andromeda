val verbosity : int ref

val annotate : bool ref

val displayable : string list ref

val message : string -> int -> ('a, Format.formatter, unit, unit) format4 -> 'a
val warning : ('a, Format.formatter, unit, unit) format4 -> 'a
val debug : ?category:string -> ('a, Format.formatter, unit, unit) format4 -> 'a

val print :
  ?max_level:int -> ?at_level:int ->
  Format.formatter -> ('a, Format.formatter, unit, unit) format4 -> 'a

val sequence : ?sep:string -> ('a -> Format.formatter -> unit) -> 'a list -> Format.formatter -> unit
val annot : ?prefix:string -> (Format.formatter -> unit) -> Format.formatter -> unit