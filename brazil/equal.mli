(** Algorithmic type equality *)
val ty : Context.t -> Syntax.ty -> Syntax.ty -> bool

(** Express a type as a product *)
val as_prod : Context.t -> Syntax.ty -> (Syntax.name * Syntax.ty * Syntax.ty) option

(** Express a type as a path type *)
val as_paths : Context.t -> Syntax.ty -> (Syntax.ty * Syntax.term * Syntax.term) option

(** Express a type as a universe *)
val as_universe : Context.t -> Syntax.ty -> Universe.t option

(** Convert a universally quantified equality to a pattern *)
val as_pattern : Context.t -> Syntax.ty -> (int * Pattern.ty * Pattern.term * Pattern.term) option
