(** Normalize a type, ignore hints. *)
val norm_ty : Syntax.ty -> Syntax.ty

(** Normalize a term, ignore hints. *)
val norm : Syntax.term -> Syntax.term

