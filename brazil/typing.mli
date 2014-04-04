
(** Synthesize the type of a term *)
val syn_term : Context.t -> Syntax.term -> Syntax.ty

(** Check the type of a term *)
val chk_term : Context.t -> Syntax.term -> unit

(** Check that two types are equal *)
val eq_type : Context.t -> Syntax.ty -> Syntax.ty -> unit

(** Check that two terms are equal *)
val eq_term : Context.t -> Syntax.term -> Syntax.term -> Syntax.ty -> unit
