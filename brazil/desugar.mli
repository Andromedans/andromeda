(** Conversion from concrete to abstract syntax. *)

(** Convert a type from concrete to abstract syntax. *)
val ty : Input.name list -> Input.ty -> Syntax.ty

(** Convert a term from concrete to abstract syntax. *)
val ty : Input.name list -> Input.term -> Syntax.term
