type t

val empty : t

val names : t -> string list

val add_var : Syntax.name -> Syntax.ty -> t -> t

val add_def : Syntax.name -> Syntax.ty -> Syntax.term -> t -> t

val add_equation : Syntax.term -> Syntax.term -> Syntax.ty -> t -> t

val add_rewrite : Syntax.term -> Syntax.term -> Syntax.ty -> t -> t

val lookup_var : Syntax.variable -> t -> Syntax.ty

val print : t -> unit
