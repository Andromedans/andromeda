(** The type of contexts. *)
type t

(** The empty context. *)
val empty : t

val print : t -> Format.formatter -> unit

val lookup_ty : Name.atom -> t -> Tt.ty option

val needed_by : loc:Location.t -> Name.atom -> t -> Name.AtomSet.t

val add : t -> Name.atom -> Tt.ty -> t option

val add_fresh : t -> Name.ident -> Tt.ty -> Name.atom * t

val recursive_assumptions : t -> Name.AtomSet.t -> Name.AtomSet.t

val restrict : t -> Name.AtomSet.t -> t

(** Remove the given atom from the context.
    Checks first that the type in the context and the type in the list are alpha equal,
    then that no atom depends on the one being removed.
    If the later case fails, the set of dependents is returned. *)
val abstract : loc:Location.t -> t -> Name.atom list -> Tt.ty list -> t

(** Join two contexts into a single one.
    Types of common atoms need to be alpha equal.
    The dependencies from the first context are used when both atoms are present. *)
val join : loc:Location.t -> t -> t -> t

(** [substitute x (ctx,e,ty)] replaces [x] in [ctx] by [e].
    It assumes that the type of [x] in [ctx] is equal to [ty]. *)
val substitute : loc:Location.t -> Name.atom -> t * Tt.term * Tt.ty -> t

(** [sort ctx] sorts the entries of [ctx] into a list so that all dependencies
    point forward in the list, ie the first atom does not depend on any atom, etc. *)
val sort : t -> Name.atom list

