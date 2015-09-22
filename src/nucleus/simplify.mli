(** Simplification of expressions and types. *)

(** [simplify] performs beta reductions when they result in a term
    that does not increase in size, for instance if the bound variable
    appears at most once in the body of the function, or if the argument
    is an atomic expression (a variable or a constant). *)
val simplify : Environment.t -> Tt.term -> Tt.term

(** [simplify_ty] simplifies a type by performing certain beta reductions,
    just like [Simplify.simplify]. *)
val simplify_ty : Environment.t -> Tt.ty -> Tt.ty
