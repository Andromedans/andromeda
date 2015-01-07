exception Error of (Location.t * string * string)

val syntax : ?loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val typing : ?loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val runtime : ?loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val exc : ?loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val verify : ?loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val fatal : ?loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val impossible : ?loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val unimplemented : ?loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
