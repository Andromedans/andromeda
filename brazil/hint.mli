
(** Prepare a type so that it can be stored as a hint. Complain if
    the type is not a universally quantified equality. *)
val prepare : Syntax.ty -> (int * Syntax.ty * Syntax.term * Syntax.term) option

(** Instantiate a hint against an equality. Assumes all inputs are normalized. *)
val instantiate : int * Syntax.ty * Syntax.term * Syntax.term ->
                    Syntax.ty -> Syntax.term -> Syntax.term -> bool

(** Instantiate as a rewrite rule.  Assumes all inputs are normalized. *)
val rewrite : int * Syntax.ty * Syntax.term * Syntax.term ->
                Syntax.ty -> Syntax.term -> Syntax.term option
