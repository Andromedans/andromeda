(** Pattern matching support for hints. *)

(** The type of patterns *)
type t

(** Given a term [e] of type [t] in abstraction [xts] (that is, the first argument is [(xts, (e,t))]),
    return a list [pvars] and a pattern [p]. The list contains those bound variables which will never
    be matched by [p]. Thus, for the purposes of beta hints the list should be empty, and for eta hints
    it should only contain bound variables whose type is equality. *)
val make : (Tt.ty, Tt.term * Tt.ty) Tt.abstraction -> Syntax.bound list * t

val pmatch : Context.t -> t -> Tt.term -> Tt.ty -> Context.t option
