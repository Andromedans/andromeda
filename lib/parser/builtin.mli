(** Predefined types and operations. *)

(** The list of built-in type, operation, and dynamic variable definitions
    corresponding to the names in Name.Predeclared, e.g.,
       - ['a list] and its constructors [[]] and [::]
       - ['a option] and its constructors [Some] and [None]
       - [coercible] and its constructors (as above)
       - operations [equal], [coerce]
       - the dynamic variable [hypotheses]
 *)
val initial : Sugared.toplevel list
