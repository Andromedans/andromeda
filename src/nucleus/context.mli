(** The type of contexts. *)
type t

type error =
  | AbstractDependency of Name.atom * Name.atom list
  | AbstractInvalidType of Name.atom * Tt.ty * Tt.ty
  | InvalidJoin of t * t * Name.atom
  | SubstitutionDependency of Name.atom * Tt.term * Name.atom
  | SubstitutionInvalidType of Name.atom * Tt.ty * Tt.ty

exception Error of error Location.located

(** The empty context. *)
val empty : t

(** Is the context empty? *)
val is_empty : t -> bool

(** Print the context. Atoms are printed according to the environment. *)
val print : penv:Tt.print_env -> t -> Format.formatter -> unit

val print_error : penv:Tt.print_env -> error -> Format.formatter -> unit

val lookup_ty : Name.atom -> t -> Tt.ty option

(** [is_subset ctx yts] returns [true] if the nodes of [ctx] are a subset of [yts]. *)
val is_subset : t -> (Name.atom * Tt.ty) list -> bool

val add_fresh : t -> Name.ident -> Tt.ty -> Name.atom * t

val recursive_assumptions : t -> Name.AtomSet.t -> Name.AtomSet.t

val restrict : t -> Name.AtomSet.t -> t

(** [abstract ctx x t] removes atom [x] from context [ctx].
    It verifies that in [ctx] the atom [x] has type [t] (using alpha equality)
    and that no atom depends on [x].
*)
val abstract : loc:Location.t -> t -> Name.atom -> Tt.ty -> t

(** Join two contexts into a single one.
    Types of common atoms need to be alpha equal.
    The dependencies from the first context are used when both atoms are present. *)
val join : loc:Location.t -> t -> t -> t

(** [substitute x (ctx,e,ty)] replaces [x] in [ctx] by [e].
    It assumes that the type of [x] in [ctx] is equal to [ty]. *)
val substitute : loc:Location.t -> Name.atom -> t * Tt.term * Tt.ty -> t

(** [elements ctx] returns the elements of [ctx] sorted into a list so that all dependencies
    point forward in the list, ie the first atom does not depend on any atom, etc. *)
val elements : t -> (Name.atom * Tt.ty) list

