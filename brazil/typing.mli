
(** Weak-head-normalization (multi-step) of a term *)
val whnfs    : Context.t -> Syntax.term -> Syntax.ty -> Syntax.term

(** Weak-head-normalization (multi-step) of a type *)
val whnfs_ty : Context.t -> Syntax.ty -> Syntax.ty

(** Algorithmic type equivalence *)
val equiv_ty : Context.t -> Syntax.ty -> Syntax.ty -> bool

(** Algorithmic term equivalence at a type *)
val equiv : Context.t -> Syntax.term -> Syntax.term -> Syntax.ty -> bool

(** Synthesize the type of a term *)
val syn_term : Context.t -> Common.debruijn Input.term -> Syntax.term * Syntax.ty

(** Check the type of a term *)
val chk_term : Context.t -> Common.debruijn Input.term -> Syntax.ty -> Syntax.term

(** Synthesize an annotated type *)
val is_type : Context.t -> Common.debruijn Input.ty -> Syntax.ty

(** Synthesize a fibered annotated type *)
val is_fibered : Context.t -> Common.debruijn Input.ty -> Syntax.ty
