(** Pretty-printing functions *)

val message : string -> int -> ('a, Format.formatter, unit, unit) format4 -> 'a
val warning : ('a, Format.formatter, unit, unit) format4 -> 'a
val debug : ('a, Format.formatter, unit, unit) format4 -> 'a

(** Print a term, possibly placing parentheses around it. We always
    print things at a given [at_level]. If the level exceeds the
    maximum allowed level [max_level] then the term should be parenthesized.

    Let us consider an example. When printing nested applications, we should print [App
    (App (a, b), c)] as ["a b c"] and [App(a, App(a, b))] as ["a (b c)"]. So
    if we assign level 1 to applications, then during printing of [App (e1, e2)] we should
    print [e1] at [max_level] 1 and [e2] at [max_level] 0. *)
val print :
  ?max_level:int -> ?at_level:int ->
  Format.formatter -> ('a, Format.formatter, unit, unit) format4 -> 'a

(** Print a sequence of things with the given (optional) separator. *)
val sequence : ?sep:string -> ('a -> Format.formatter -> unit) -> 'a list -> Format.formatter -> unit
