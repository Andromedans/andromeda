
(** Synthesize the type of a term *)
val syn_term : Context.t -> Common.debruijn Input.term -> Syntax.term * Syntax.ty

(** Check the type of a term *)
val chk_term : Context.t -> Common.debruijn Input.term -> Syntax.ty -> Syntax.term
