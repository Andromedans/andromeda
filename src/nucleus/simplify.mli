(** Simplification of expressions and types. *)

(** [termimplify] performs beta reductions when they result in a term
    that does not increase in size, for instance if the bound variable
    appears at most once in the body of the function, or if the argument
    is an atomic expression (a variable or a constant). *)
val term : Environment.t -> Tt.term -> Tt.term

(** [ty] simplifies a type by performing certain beta reductions, just like [term]. *)
val ty : Environment.t -> Tt.ty -> Tt.ty

(** [context] simplifies a context by performing certain beta reductions, just like [term]. *)
val context : Environment.t -> Context.t -> Context.t
