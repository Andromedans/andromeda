(** Synthesize the type of a term *)
val syn_term : Context.t -> Common.debruijn Input.term -> Syntax.term * Syntax.ty

(** Check the type of a term *)
val chk_term : Context.t -> Common.debruijn Input.term -> Syntax.ty -> Syntax.term

(** Synthesize an annotated type *)
val is_type : Context.t -> Common.debruijn Input.ty -> Syntax.ty

(** Synthesize a fibered annotated type *)
val is_fibered : Context.t -> Common.debruijn Input.ty -> Syntax.ty

