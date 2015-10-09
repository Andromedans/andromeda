(** The type of contexts, currently dummy. *)
type t

(** The empty context. *)
val empty : t

(** Join two contexts into a single one. Return the new context
    and a list of equations that need to be satisfied in order
    for the contexts to be joinable. *)
val join : t -> t -> t * (t * Tt.ty * Tt.ty) list

(** Remove the given atoms from the context, in the order
    given by the list. Fails if this is not doable. *)
val abstract : t -> Name.atom list -> t


val lookup : t -> Name.atom -> Tt.ty
