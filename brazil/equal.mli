(** Algorithmic type equality *)
val equal_ty : Context.t -> Syntax.ty -> Syntax.ty -> bool

(** Express a type as a product *)
val as_prod : Context.t -> Syntax.ty -> (Syntax.name * Syntax.ty * Syntax.ty) option

(** Express a type as a path type *)
val as_paths : Context.t -> Syntax.ty -> (Syntax.ty * Syntax.term * Syntax.term) option

(** Express a type as a universe *)
val as_universe : Context.t -> Syntax.ty -> Universe.t option

(** Convert a universally quantified equality to a pattern *)
val as_hint : Context.t -> Syntax.term -> Syntax.ty -> Context.hint

(** Weak-head normalize a type *)
val whnf_ty : use_rws:bool -> Context.t -> Syntax.ty -> Syntax.ty

(** Weak-head normalize a term *)
val whnf : use_rws:bool -> Context.t -> Syntax.ty -> Syntax.term -> Syntax.term

(** Extract the type of an annotated term *)
val type_of : Context.t -> Syntax.term -> Syntax.ty
