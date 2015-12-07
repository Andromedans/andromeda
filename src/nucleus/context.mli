(** The type of contexts. *)
type t

(** The empty context. *)
val empty : t

val print : t -> Format.formatter -> unit

val lookup_ty : Name.atom -> t -> Tt.ty option

val add : t -> Name.atom -> Tt.ty -> t option

val add_fresh : t -> Name.ident -> Tt.ty -> Name.atom * t

val restrict : t -> Name.AtomSet.t -> t

(** Remove the given atom from the context.
    Fails if this is not doable.
    Also checks that the types are alpha equal. *)
type ('a,'b) err =
  | OK of 'a
  | Err of 'b

val abstract : loc:Location.t -> t -> Name.atom -> Tt.ty -> (t,Name.AtomSet.t) err

(** Join two contexts into a single one.
    Types of common atoms need to be alpha equal.
    The dependencies from the first context are used when both atoms are present. *)
val join : t -> t -> t

(** [substitute x (ctx,e,ty)] replaces [x] in [ctx] by [e].
    It assumes that the type of [x] in [ctx] is equal to [ty]. *)
val substitute : loc:Location.t -> Name.atom -> t * Tt.term * Tt.ty -> t

