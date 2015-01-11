(** The type of contexts *)
type t

(** The empty context *)
val empty : t

(** Known meta variables *)
val metas : t -> Name.t list

(** Lookup a free variable. *)
val lookup_free : Name.t -> t -> Tt.ty option

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : Syntax.bound -> t -> Name.t * Tt.ty

(** Lookup a meta variable. *)
val lookup_meta : Syntax.bound -> t -> Value.value

(** Add a free variable of a given type to the context.
    Fails if the free variable is already bound. *)
val add_free : Name.t -> Tt.ty -> t -> t 

(** [add_fresh x t ctx] adds a fresh free variable with suggested
    name [x] of given type [t] to the context [ctx]. Return the
    actual name and the new context. *)
val add_fresh : Name.t -> Tt.ty -> t -> Name.t * t

(** Add a meta variable with suggested name to the context. *)
val add_meta : Name.t -> Value.value -> t -> t

val print : t -> Format.formatter -> unit
