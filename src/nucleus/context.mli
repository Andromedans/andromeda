(** The type of contexts, currently dummy. *)
type t

(** The empty context. *)
val empty : t

(** Joint two contexts into a single one. Return the new context
    and a list of equations that need to be satisfied in order
    for the contexts to be joinable. *)
val join : t -> t -> t * (t * Tt.ty * Tt.ty) list
