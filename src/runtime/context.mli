(** The type of contexts *)
type t

(** The empty context *)
val empty : t

(** Known bound variables *)
val bound_names : t -> Name.t list

(** Variable names already used in the context *)
val used_names : t -> Name.t list

(** Lookup a free variable. *)
val lookup_free : Name.t -> t -> Tt.ty option

(** Lookup a free variable by its de Bruijn index *)
val lookup_bound : Syntax.bound -> t -> Value.value

(** Add a free variable of a given type to the context.
    Fails if the free variable is already bound. *)
val add_free : Name.t -> Tt.ty -> t -> t 

(** [add_fresh x t ctx] adds a fresh free variable with suggested
    name [x] of given type [t] to the context [ctx]. Return the
    actual name and the new context. *)
val add_fresh : Name.t -> Tt.ty -> t -> Name.t * t

(** Add a bound variable with given name to the context. *)
val add_bound : Name.t -> Value.value -> t -> t

val print : t -> Format.formatter -> unit
