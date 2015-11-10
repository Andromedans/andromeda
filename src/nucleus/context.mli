(** The type of contexts, currently dummy. *)
type t

(** The empty context. *)
val empty : t

val print : t -> Format.formatter -> unit

val lookup_ty : Name.atom -> t -> Tt.ty option

(** [cone ctx x t] returns a context with a fresh atom [y]
    of type [t], which depends on everything in [ctx]. The assumption
    here is that [t] is a type in [ctx]. The function is called
    [cone] because it produces a cone in the graph-theoretic and topological
    sense of word. *)
val cone : t -> Name.ident -> Tt.ty -> Name.atom * t

(** [context_at ctx x] returns the smallest subcontext of [ctx] where the type of [x] is valid.
    Not_found is raised if [x] does not belong to [ctx]. *)
val context_at : t -> Name.atom -> t

(** Remove the given atoms from the context, in the order
    given by the list. Fails if this is not doable. *)
val abstract : loc:Location.t -> t -> Name.atom list -> t

(** Join two contexts into a single one. Return the new context
    and a list of equations that need to be satisfied in order
    for the contexts to be joinable. *)
val join : t -> t -> t

(** [substitute ctx x (ctxe,e,ty_e)] replaces [x] in [ctx] by [e].
    It assumes that the type of [x] in [ctx] is equal to the type of [e] under [ctxe]. *)
val substitute : t -> Name.atom -> t * Tt.term * Tt.ty -> t

(** The following does not seem to be used? *)
type renaming

val rename : t -> renaming -> t

val refresh : t -> t * renaming

