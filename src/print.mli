val verbosity : int ref

val annotate : bool ref

val displayable : string list ref

val message : string -> int -> ('a, Format.formatter, unit, unit) format4 -> 'a
val error : 'a * string * string -> unit
val warning : ('a, Format.formatter, unit, unit) format4 -> 'a
val debug : ?category:string -> ('a, Format.formatter, unit, unit) format4 -> 'a

val print : Format.formatter -> ('a, Format.formatter, unit, unit) format4 -> 'a

val name : Common.name -> Format.formatter -> unit

val value : Context.t -> Value.value -> Format.formatter -> unit

val ty : Context.t -> Value.ty -> Format.formatter -> unit

val context : Context.t -> Format.formatter -> unit
