(** Simplification of expressions and types. *)

(** [value v] performs beta reductions in the terms of [v] when they result in a term
    that does not increase in size, for instance if the bound variable
    appears at most once in the body of the function, or if the argument
    is an atomic expression (a variable or a constant). *)
val value : Runtime.env -> Runtime.value -> Runtime.value

