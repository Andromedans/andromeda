type t

val empty : t

val names : t -> string list

val add_var : Syntax.name -> Syntax.ty -> t -> t

val add_vars : (Syntax.name * Syntax.ty) list -> t -> t

val add_def : Syntax.name -> Syntax.ty -> Syntax.term -> t -> t

val add_equation : Syntax.term -> Syntax.ty -> (int * Pattern.ty * Pattern.term * Pattern.term) -> t -> t

val add_rewrite : Syntax.term -> Syntax.ty -> (int * Pattern.ty * Pattern.term * Pattern.term) -> t -> t

val lookup_var : Syntax.variable -> t -> Syntax.ty

val rewrites : t -> (int * Pattern.ty * Pattern.term * Pattern.term) list

val equations : t -> (int * Pattern.ty * Pattern.term * Pattern.term) list

val print : t -> unit
