(** Conversion from concrete to abstract syntax. *)

(** Convert a type from concrete to abstract syntax. *)
val ty : Input.variable list -> Input.ty -> Syntax.ty

(** Convert a term from concrete to abstract syntax. *)
val ty : Input.variable list -> Input.term -> Syntax.term
