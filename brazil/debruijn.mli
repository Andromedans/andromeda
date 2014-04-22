(** Conversion from concrete to abstract syntax. *)

(** Convert a type from concrete to abstract syntax. *)
val ty : Common.name list -> Common.name Input.ty -> Common.debruijn Input.ty

(** Convert a term from concrete to abstract syntax. *)
val term : Common.name list -> Common.name Input.term -> Common.debruijn Input.term
