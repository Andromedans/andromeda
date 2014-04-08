type t

val empty : t

val add_var : Syntax.variable -> Syntax.ty -> t -> t

val add_hint : Syntax.term -> Syntax.term -> Syntax.ty -> t -> t

val lookup_var : Syntax.variable -> t -> Syntax.ty option


