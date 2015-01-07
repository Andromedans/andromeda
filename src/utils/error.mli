exception Error of (Position.t * string * string)

val syntax : ?loc:Position.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val typing : ?loc:Position.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val runtime : ?loc:Position.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val exc : ?loc:Position.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val verify : ?loc:Position.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val fatal : ?loc:Position.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val impossible : ?loc:Position.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val unimplemented : ?loc:Position.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
